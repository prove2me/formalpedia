-- Prove2me | Theorems.Thm_NeymanPearsonClassification_random_sampling_oracle_inequality
-- name    : NeymanPearsonClassification.random_sampling_oracle_inequality
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:46:04.673714+00:00
-- url     : https://prove2.me/theorems/1f425c9c-5993-4753-9ccf-3f0236895906
-- title:
--   Corollary 4.1: the NP classifier under i.i.d. labelled sampling
-- statement:
--   Let $\varphi,\kappa,\delta,\alpha$ and the base classifiers be as in Theorem 4.1, let Assumption 1 hold, and let $\bar\varepsilon$ and $n_0$ be as in Theorem 4.2. Let $(X_1,Y_1),\dots,(X_n,Y_n)$ be independent copies of $(X,Y)$, where $Y\in\{-1,1\}$, $p=\mathbb P(Y=1)\in(0,1)$, and $X$ has law $P^-$ given $Y=-1$ and $P^+$ given $Y=1$. Let $N^-=\#\{i:Y_i=-1\}$ and $N^+=n-N^-$, and let $\tilde h^\kappa_n$ be any solution of the program (3.4) built from the two label classes of the sample. If $n>2n_0/(1-p)$, then:
--
--   1. With probability at least $(1-2\delta)(1-e^{-n(1-p)^2/2})$,
--   $$R^-(\tilde h^\kappa_n)\le R^-_\varphi(\tilde h^\kappa_n)\le\alpha\quad\text{and}\quad R^+_\varphi(\tilde h^\kappa_n)-\min_{h\in\mathcal H^{\varphi,\alpha}}R^+_\varphi(h)\le\frac{4\varphi(1)\kappa}{(1-\bar\varepsilon)\alpha\sqrt{N^-}}+\frac{2\kappa}{\sqrt{N^+}}.$$
--   2. With probability at least $1-2\delta-e^{-n(1-p)^2/2}-e^{-np^2/2}$,
--   $$R^-(\tilde h^\kappa_n)\le R^-_\varphi(\tilde h^\kappa_n)\le\alpha\quad\text{and}\quad R^+_\varphi(\tilde h^\kappa_n)-\min_{h\in\mathcal H^{\varphi,\alpha}}R^+_\varphi(h)\le\frac{4\sqrt2\,\varphi(1)\kappa}{(1-\bar\varepsilon)\alpha\sqrt{n(1-p)}}+\frac{2\sqrt2\,\kappa}{\sqrt{np}}.$$
--
--   **Formalization Note** The law of each pair is given by $\mathbb P(X_i\in A,Y_i=1)=p\,P^+(A)$ and $\mathbb P(X_i\in A,Y_i=-1)=(1-p)P^-(A)$. In part 1 the paper's convention $1/\sqrt0=+\infty$ is made explicit. When $N^-=0$ the paper's program (3.4) is undefined; part 1 excludes that case by an explicit guard $N^->0$ (in Lean, with an empty sample the level $\alpha-\kappa/\sqrt0$ evaluates to $\alpha$ and $\hat R^-_\varphi$ to $0$, so junk solutions would exist). When $N^+=0$ the type II bound is $+\infty$, so only the type I bound is required. Part 2 has no guard: on $\{N^-=0\}$ or $\{N^+=0\}$ the Lean program has such junk solutions, but these events lie inside $\{N^-<n(1-p)/2\}$ and $\{N^+<np/2\}$, whose probabilities are already part of the failure bound, so part 2 remains true as stated. "Any solution" is stated uniformly over all solutions, as in Theorem 4.2.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Section 4.3, Corollary 4.1, eqs. (4.7), (4.8), (4.9), p. 10; proof in Section 6.5, pp. 18-19

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

theorem random_sampling_oracle_inequality {d M : ℕ} (hM : 2 ≤ M)
    (h : Fin M → EuclideanSpace ℝ (Fin d) → ℝ) (hh : IsBaseFamily h)
    (Pm Pp : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pm] [IsProbabilityMeasure Pp]
    (φ : ℝ → ℝ) (hφ : IsConvexSurrogate φ) (L : ℝ) (hL : 0 < L) (hLip : LipschitzOnWith (Real.toNNReal L) φ (Set.Icc (-1) 1))
    (δ α : ℝ) (hδ : δ ∈ Set.Ioo 0 1) (hα : α ∈ Set.Ioo 0 1)
    (hA1 : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (Hphi h Pm φ (ε * α)).Nonempty)
    (p : ℝ) (hp : p ∈ Set.Ioo 0 1) {n : ℕ}
    (hn : 2 * (nZero (kappa L M δ) (epsBar h Pm φ α) α : ℝ) / (1 - p) < n)
    {Omega : Type*} [MeasurableSpace Omega] (μ : Measure Omega) [IsProbabilityMeasure μ]
    (X : Fin n → Omega → EuclideanSpace ℝ (Fin d)) (Y : Fin n → Omega → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hind : iIndepFun (fun i ω => (X i ω, Y i ω)) μ)
    (hY : ∀ i ω, Y i ω = -1 ∨ Y i ω = 1)
    (hlawp : ∀ i (A : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet A →
      μ {ω | X i ω ∈ A ∧ Y i ω = 1} = ENNReal.ofReal p * Pp A)
    (hlawm : ∀ i (A : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet A →
      μ {ω | X i ω ∈ A ∧ Y i ω = -1} = ENNReal.ofReal (1 - p) * Pm A) :
    μ {ω | ¬ (0 < (labelIdx (fun i => Y i ω) (-1)).card →
        ∀ f, IsNPClassifier h φ α (kappa L M δ) (labelIdx (fun i => Y i ω) (-1)) (fun i => X i ω)
            (labelIdx (fun i => Y i ω) 1) (fun i => X i ω) f →
          (typeI Pm f ≤ phiTypeI Pm φ f ∧ phiTypeI Pm φ f ≤ α) ∧
          (0 < (labelIdx (fun i => Y i ω) 1).card →
            phiTypeII Pp φ f - minPhiTypeII h Pm Pp φ α ≤
              4 * φ 1 * kappa L M δ /
                  ((1 - epsBar h Pm φ α) * α * Real.sqrt (labelIdx (fun i => Y i ω) (-1)).card) +
                2 * kappa L M δ / Real.sqrt (labelIdx (fun i => Y i ω) 1).card))} ≤
      ENNReal.ofReal (1 - (1 - 2 * δ) * (1 - Real.exp (-(n * (1 - p) ^ 2 / 2)))) ∧
    μ {ω | ¬ ∀ f, IsNPClassifier h φ α (kappa L M δ) (labelIdx (fun i => Y i ω) (-1))
          (fun i => X i ω) (labelIdx (fun i => Y i ω) 1) (fun i => X i ω) f →
        (typeI Pm f ≤ phiTypeI Pm φ f ∧ phiTypeI Pm φ f ≤ α) ∧
        phiTypeII Pp φ f - minPhiTypeII h Pm Pp φ α ≤
          4 * Real.sqrt 2 * φ 1 * kappa L M δ /
              ((1 - epsBar h Pm φ α) * α * Real.sqrt (n * (1 - p))) +
            2 * Real.sqrt 2 * kappa L M δ / Real.sqrt (n * p)} ≤
      ENNReal.ofReal (2 * δ + Real.exp (-(n * (1 - p) ^ 2 / 2)) + Real.exp (-(n * p ^ 2 / 2))) := by sorry

end NeymanPearsonClassification
