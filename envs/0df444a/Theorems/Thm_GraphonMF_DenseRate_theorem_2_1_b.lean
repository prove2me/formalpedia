-- Prove2me | Theorems.Thm_GraphonMF_DenseRate_theorem_2_1_b
-- name    : GraphonMF.DenseRate.theorem_2_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:52.628489+00:00
-- url     : https://prove2.me/theorems/26db4bfd-1e72-49c6-a96b-5e5fe6985bc7
-- title:
--   Theorem 2.1(b), p. 3593 — under Condition 2.3, W_{2,T}(μ_u, μ_v) ≤ κ|u − v| on each interval Iᵢ
-- statement:
--   Let $G$ be a graphon, let $b,\sigma$ and the initial laws $\mu_u(0)$ satisfy Condition 2.1, and let $X=(X_u)_{u\in I}$ solve the graphon particle system (2.1), with path laws $\mu_u=\mathcal L(X_u)\in\mathcal P(\mathcal C_d)$. Suppose Condition 2.3 holds for the intervals $I_1,\dots,I_N$ covering $I$: the initial laws are $W_2$-Lipschitz in $u$ on each $I_i$ and $G$ is Lipschitz on each block $I_i\times I_j$.
--
--   Then there is a constant $\kappa\in(0,\infty)$ such that
--   $$W_{2,T}(\mu_u,\mu_v)\le\kappa|u-v|\qquad\text{whenever }u,v\in I_i\text{ for some }i\in\{1,\dots,N\}.$$
--
--   Lipschitz dependence of the path law on the label is what turns the Riemann-sum discretization of the graphon interaction into an $O(1/n)$ error in the proof of Theorem 3.2.
--
--   **Formalization Note.** The intervals are those of the Condition 2.3 hypothesis, passed as an explicit family `J : Fin N → Set I`; $W_{2,T}$ is the published Wasserstein distance of order 2 on $\mathcal C_d$ with the uniform norm, valued in $[0,\infty]$.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), https://doi.org/10.1214/22-AAP1901, p. 3593, Theorem 2.1(b)

import Mathlib
import Definitions.Def_GraphonMF_DenseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped ENNReal NNReal

namespace GraphonMF.DenseRate

theorem theorem_2_1_b {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (P : Measure Ω) (μ0 : I → Measure (Fin d → ℝ)) (X0 : I → Ω → (Fin d → ℝ))
    (B : I → ℝ≥0 → Ω → Fin d → ℝ) (hN : NoiseSetting P μ0 X0 B)
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (sigma : (Fin d → ℝ) → (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hε : 0 < ε) (h21 : Cond21 ε μ0 b sigma)
    (G : I → I → ℝ) (hG : IsGraphon G)
    {N : ℕ} (J : Fin N → Set I) (h23 : Cond23 μ0 G J)
    (X : I → ℝ≥0 → Ω → (Fin d → ℝ)) (hX : IsGraphonSolution T P X0 B G b sigma X) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ k : Fin N, ∀ u ∈ J k, ∀ v ∈ J k,
      W2T (law T P (X u)) (law T P (X v)) ≤ ENNReal.ofReal (κ * |(u : ℝ) - v|) := by sorry

end GraphonMF.DenseRate
