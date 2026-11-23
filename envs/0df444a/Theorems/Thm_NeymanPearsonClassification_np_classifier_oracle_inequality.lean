-- Prove2me | Theorems.Thm_NeymanPearsonClassification_np_classifier_oracle_inequality
-- name    : NeymanPearsonClassification.np_classifier_oracle_inequality
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:44:42.814574+00:00
-- url     : https://prove2.me/theorems/f3624b22-158a-4c04-8b73-a36dbb53efe3
-- title:
--   Theorem 4.2: type I control and type II oracle inequality for the convexified NP classifier
-- statement:
--   Let $\delta,\alpha\in(0,1)$, $L>0$, and let $\varphi$ be an $L$-Lipschitz convex surrogate. Let $h_1,\dots,h_M$, $M\ge2$, be measurable base classifiers with values in $[-1,1]$, and $\kappa=4\sqrt2\,L\sqrt{\log(2M/\delta)}$. Assume (Assumption 1) that there is $\varepsilon\in(0,1)$ with $\mathcal H^{\varphi,\varepsilon\alpha}\neq\emptyset$. Let $\bar\varepsilon$ be the smallest such $\varepsilon$ and $n_0=\lceil(4\kappa/((1-\bar\varepsilon)\alpha))^2\rceil$.
--
--   Let $X^-_1,\dots,X^-_{n^-}$ be i.i.d. with law $P^-$ and $X^+_1,\dots,X^+_{n^+}$ i.i.d. with law $P^+$. The two samples need not be independent of each other. Assume $n^+\ge1$ and $n^-\ge n_0$. Let $\tilde h^\kappa$ be any solution of
--
--   $$\min_{h\in\mathcal H^{\mathrm{conv}},\ \hat R^-_\varphi(h)\le\alpha-\kappa/\sqrt{n^-}}\hat R^+_\varphi(h).$$
--
--   Then, with probability at least $1-2\delta$,
--
--   $$R^-(\tilde h^\kappa)\le R^-_\varphi(\tilde h^\kappa)\le\alpha$$
--
--   and
--
--   $$R^+_\varphi(\tilde h^\kappa)-\min_{h\in\mathcal H^{\varphi,\alpha}}R^+_\varphi(h)\le\frac{4\varphi(1)\kappa}{(1-\bar\varepsilon)\alpha\sqrt{n^-}}+\frac{2\kappa}{\sqrt{n^+}}.$$
--
--   This is the paper's main result: the convexified NP classifier respects the type I level $\alpha$ with high probability and has near-optimal $\varphi$-type II error.
--
--   **Formalization Note** "Any solution" is stated uniformly: on one event of probability at least $1-2\delta$, every solution of the empirical program satisfies both bounds. The minimum over $\mathcal H^{\varphi,\alpha}$ is an infimum over a nonempty set. The asymptotic $O(\cdot)$ remark that follows the theorem is not included.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Section 4.2, Theorem 4.2, eqs. (3.4), (4.3), (4.4), (4.5), Assumption 1, p. 9; proof in Section 6.4, pp. 17-18

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

theorem np_classifier_oracle_inequality {d M : ℕ} (hM : 2 ≤ M)
    (h : Fin M → EuclideanSpace ℝ (Fin d) → ℝ) (hh : IsBaseFamily h)
    (Pm Pp : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pm] [IsProbabilityMeasure Pp]
    (φ : ℝ → ℝ) (hφ : IsConvexSurrogate φ) (L : ℝ) (hL : 0 < L) (hLip : LipschitzOnWith (Real.toNNReal L) φ (Set.Icc (-1) 1))
    (δ α : ℝ) (hδ : δ ∈ Set.Ioo 0 1) (hα : α ∈ Set.Ioo 0 1)
    (hA1 : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (Hphi h Pm φ (ε * α)).Nonempty)
    {nm np : ℕ} (hnm1 : 1 ≤ nm) (hnp : 1 ≤ np)
    (hnm : nZero (kappa L M δ) (epsBar h Pm φ α) α ≤ nm)
    {Omega : Type*} [MeasurableSpace Omega] (μ : Measure Omega) [IsProbabilityMeasure μ]
    (Xm : Fin nm → Omega → EuclideanSpace ℝ (Fin d)) (Xp : Fin np → Omega → EuclideanSpace ℝ (Fin d))
    (hXm : ∀ i, Measurable (Xm i)) (hXp : ∀ i, Measurable (Xp i))
    (hXmind : iIndepFun Xm μ) (hXpind : iIndepFun Xp μ)
    (hXmlaw : ∀ i, μ.map (Xm i) = Pm) (hXplaw : ∀ i, μ.map (Xp i) = Pp) :
    μ {ω | ¬ ∀ f, IsNPClassifier h φ α (kappa L M δ) Finset.univ (fun i => Xm i ω)
        Finset.univ (fun i => Xp i ω) f →
      (typeI Pm f ≤ phiTypeI Pm φ f ∧ phiTypeI Pm φ f ≤ α) ∧
      phiTypeII Pp φ f - minPhiTypeII h Pm Pp φ α ≤
        4 * φ 1 * kappa L M δ / ((1 - epsBar h Pm φ α) * α * Real.sqrt nm) +
          2 * kappa L M δ / Real.sqrt np} ≤ ENNReal.ofReal (2 * δ) := by sorry

end NeymanPearsonClassification
