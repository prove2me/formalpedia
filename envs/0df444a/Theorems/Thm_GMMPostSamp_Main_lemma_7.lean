-- Prove2me | Theorems.Thm_GMMPostSamp_Main_lemma_7
-- name    : GMMPostSamp.Main.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:28:53.349199+00:00
-- url     : https://prove2.me/theorems/b486160d-3833-49fd-bf0d-45df79bf86b4
-- title:
--   Lemma 7 — on E: min w_i ≥ τ/2, λI ⪯ ∇²V, λI ⪯ ∇²V_c ⪯ LI on B × S_k, and the true means are 1-separated
-- statement:
--   There are an admissible LearnGMM program (with the guarantee and runtime of Proposition 4) and a universal $C>0$ such that for all $k,d,n\ge1$, $\sigma>0$, $0<a\le A$, $\alpha\in[a,A]^k$, $\delta\in(0,\frac16)$, with $\tau=\frac1{Ak}(\frac\delta{8k})^{1/a}$ and $K=C(\frac1{\tau^3}+\frac1{\sigma^6})$: if $0<r\le\frac{\tau^2}{CK(1+\sigma^6)}$, $d\ge C(k+\log\frac1\delta)$ and
--   $$n\ge\frac{C(1+\sigma^{12})}{\tau^4}\Big(\frac1{\tau^2}+\frac d{\sigma^2}\Big)^2\log\frac d\delta+Cd^{3/2}$$
--   (together with Proposition 4's hypotheses), then outside an event of probability at most $\delta$ over Model 1 and the tapes, Proposition 4's conclusions hold and for all $(\theta,c)\in B\times S_k$:
--   $$\min_iw_i\ge\frac\tau2,\qquad\lambda I\preceq\nabla^2V(\theta),\qquad\lambda I\preceq\nabla^2V_c(\theta)\preceq LI,\qquad\lambda=\frac{n\tau^2}{3200(1+\sigma^2)^3},\ L=8n\Big(\frac1{\tau^2}+\frac1{\sigma^2}\Big),$$
--   and $\|\mu^\star_i-\mu^\star_j\|_2\ge1$ for all $i\ne j$. These are the curvature bounds behind Corollary 1 and the oracle of Proposition 5.
--
--   **Formalization Note.** Hessians are second directional derivatives along tangent vectors of (51).
--
--   Differences from the source:
--   - reading: under the same event E as in Proposition 4 (which occurs with probability ≥ 1 − δ over Model 1 and Algorithm 3) → ∃ one admissible LearnGMM program with Proposition 4's runtime and an event of probability ≥ 1 − δ over Model 1 ⊗ tapes on which Proposition 4's conclusions and Lemma 7's conclusions both hold; Proposition 4's hypotheses r < 1/6 and n ≥ C d³k¹¹(1+σ⁸)/(τ⁶r²) included; reason: E is Proposition 4's event (strengthened in the proof, p. 45); the two statements share it
--   - encoding: ∇²V, ∇²V_c in orthonormal affine coordinates on Θ, λI_d ⪯ … ⪯ LI_d → λ‖v‖² ≤ d²/dt² F(θ + tv)|₀ ≤ L‖v‖² for every v in the tangent space T of (51), ‖v‖ Euclidean; reason: the Hessian quadratic form in orthonormal coordinates of the affine hull; I_d is the identity on T
--   - reading: 'There is a universal constant C > 0' → ∃ C > 0 quantified before all parameters, also used for Proposition 4's constants; reason: C is universal
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 22, Lemma 7

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model
import Definitions.Def_GMMPostSamp_Main_Machine

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Lemma 7 (p. 22): there are a program LearnGMM (with the guarantee of Proposition 4) and a
universal `C` such that, under the hypotheses below, outside an event of probability at most `δ`
over Model 1 and the program's tapes the conclusions of Proposition 4 hold and also, for all
`(θ, c) ∈ B × S_k`: `min_i w_i ≥ τ/2`, `λ I ⪯ ∇²V(θ)`, `λ I ⪯ ∇²V_c(θ) ⪯ L I` (orthonormal affine
coordinates on `Θ`), with `λ = nτ²/(3200(1 + σ²)³)`, `L = 8n(1/τ² + 1/σ²)`; moreover the true
means are pairwise at distance at least `1`. -/
theorem lemma_7 : ∃ L : Machine.Program, Machine.Admissible L ∧ ∃ C : ℝ, 0 < C ∧
    ∀ k d n : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ n → ∀ (σ a A δ r : ℝ) (α : Fin k → ℝ),
      0 < σ → 0 < a → a ≤ A → (∀ i, α i ∈ Set.Icc a A) → 0 < δ → δ < 1 / 6 →
      let τ : ℝ := (1 / (A * k)) * (δ / (8 * k)) ^ (1 / a)
      let K : ℝ := C * (1 / τ ^ 3 + 1 / σ ^ 6)
      0 < r → r ≤ τ ^ 2 / (C * K * (1 + σ ^ 6)) → r < 1 / 6 →
      C * ((k : ℝ) + Real.log (1 / δ)) ≤ d →
      C * (1 + σ ^ 12) / τ ^ 4 * (1 / τ ^ 2 + d / σ ^ 2) ^ 2 * Real.log (d / δ) +
          C * (d : ℝ) ^ ((3 : ℝ) / 2) ≤ n →
      C * ((d : ℝ) ^ 3 * (k : ℝ) ^ 11 * (1 + σ ^ 8) / (τ ^ 6 * r ^ 2)) ≤ n →
      (∀ x : Fin n → E d, Machine.HaltsWithin L
          ([(k : ℝ), (d : ℝ), (n : ℝ), δ] ++ Machine.dataCells x)
          (C * (n * (d : ℝ) ^ 2 + n * (k : ℝ) ^ 3) + C)) ∧
      ((joint k d n σ α).prod Machine.tapeLaw) {q | ¬ ∃ θbar : Param k d,
          (Machine.finalState L Machine.noOracle
              ([(k : ℝ), (d : ℝ), (n : ℝ), δ] ++ Machine.dataCells q.1.2.2) q.2).map
              (Machine.decodeParam k d) = some θbar ∧
            θbar ∈ Theta k d ∧ OrbitClose θbar q.1.1 r ∧ OrbitDisjoint θbar (3 * r) ∧
            (∀ θ ∈ ballB θbar (3 * r), (∀ i, τ / 2 ≤ θ.1 i) ∧
              HessGe (potV σ α q.1.2.2) θ (n * τ ^ 2 / (3200 * (1 + σ ^ 2) ^ 3)) ∧
              ∀ c, HessBetween (potVc σ α q.1.2.2 c) θ (n * τ ^ 2 / (3200 * (1 + σ ^ 2) ^ 3))
                (8 * n * (1 / τ ^ 2 + 1 / σ ^ 2))) ∧
            ∀ i j, i ≠ j → 1 ≤ ‖q.1.1.2 i - q.1.1.2 j‖}
        ≤ ENNReal.ofReal δ := by sorry

end GMMPostSamp.Main
