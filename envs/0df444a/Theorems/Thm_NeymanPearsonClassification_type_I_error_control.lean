-- Prove2me | Theorems.Thm_NeymanPearsonClassification_type_I_error_control
-- name    : NeymanPearsonClassification.type_I_error_control
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:42:26.301914+00:00
-- url     : https://prove2.me/theorems/d19e75e9-2cc7-4203-8ee9-27caf130bf45
-- title:
--   Theorem 4.1: control of the type I error
-- statement:
--   Let $\delta,\alpha\in(0,1)$, $L>0$, and let $\varphi$ be an $L$-Lipschitz convex surrogate. Let $h_1,\dots,h_M$, $M\ge2$, be measurable base classifiers with values in $[-1,1]$, and let $X^-_1,\dots,X^-_{n^-}$, $n^-\ge1$, be i.i.d. with law $P^-$. Put $\kappa=4\sqrt2\,L\sqrt{\log(2M/\delta)}$ and $\alpha_\kappa=\alpha-\kappa/\sqrt{n^-}$. Then, with probability at least $1-\delta$, every $h\in\mathcal H^{\mathrm{conv}}$ with $\hat R^-_\varphi(h)\le\alpha_\kappa$ satisfies
--
--   $$R^-(h)\le R^-_\varphi(h)\le\alpha,$$
--
--   that is, $\mathbb P\big[\mathcal H^{\varphi,\alpha_\kappa}_{n^-}\subset\mathcal H^{\varphi,\alpha}\big]\ge1-\delta$ (eq. 4.1).
--
--   So a strengthened empirical constraint guarantees the prescribed level $\alpha$ for the true type I error, with high probability.
--
--   **Formalization Note** The theorem's "any (random) classifier $h$" is stated in the equivalent uniform form (4.1): on one event of probability at least $1-\delta$ the bound holds for every classifier satisfying the empirical constraint, so it holds for every data-dependent choice.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Section 4.1, Theorem 4.1, eq. (4.1), p. 8; proof in Section 6.2, p. 15

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

theorem type_I_error_control {d M : ℕ} (hM : 2 ≤ M)
    (h : Fin M → EuclideanSpace ℝ (Fin d) → ℝ) (hh : IsBaseFamily h)
    (Pm Pp : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pm] [IsProbabilityMeasure Pp]
    (φ : ℝ → ℝ) (hφ : IsConvexSurrogate φ) (L : ℝ) (hL : 0 < L) (hLip : LipschitzOnWith (Real.toNNReal L) φ (Set.Icc (-1) 1))
    (δ α : ℝ) (hδ : δ ∈ Set.Ioo 0 1) (hα : α ∈ Set.Ioo 0 1)
    {nm : ℕ} (hnm : 1 ≤ nm)
    {Omega : Type*} [MeasurableSpace Omega] (μ : Measure Omega) [IsProbabilityMeasure μ]
    (Xm : Fin nm → Omega → EuclideanSpace ℝ (Fin d)) (hXm : ∀ i, Measurable (Xm i))
    (hXind : iIndepFun Xm μ) (hXlaw : ∀ i, μ.map (Xm i) = Pm) :
    μ {ω | ¬ ∀ f ∈ HphiEmp h φ Finset.univ (fun i => Xm i ω) (α - kappa L M δ / Real.sqrt nm),
      typeI Pm f ≤ phiTypeI Pm φ f ∧ phiTypeI Pm φ f ≤ α} ≤ ENNReal.ofReal δ := by sorry

end NeymanPearsonClassification
