-- Prove2me | Theorems.Thm_GraphonMF_SparseRate_theorem_2_1_b
-- name    : GraphonMF.SparseRate.theorem_2_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:31.795973+00:00
-- url     : https://prove2.me/theorems/7ad5a08c-0b4f-4bb5-91b3-ff5342a06d56
-- title:
--   Theorem 2.1(b), p. 3593, for the limit system (4.2) — W_{2,T}(μ_u, μ_v) ≤ κ|u − v| on each interval of Condition 2.3
-- statement:
--   Let $b$ and $\sigma$ satisfy Condition 4.1(b),(c), let the initial laws $\mu_u(0)$ satisfy Condition 4.1(a), let $G$ be a graphon, and suppose Condition 2.3 holds with intervals $I_1,\dots,I_N$ covering $I$. Let $X=(X_u)_{u\in I}$ solve the graphon particle system (4.2) and let $\mu_u=\mathcal L(X_u)\in\mathcal P(\mathcal C_d)$. Then there is $\kappa\in(0,\infty)$ such that
--   $$W_{2,T}(\mu_u,\mu_v)\le\kappa\,|u-v|\qquad\text{whenever }u,v\in I_i\text{ for some }i\in\{1,\dots,N\}.$$
--
--   The law of the graphon particle depends Lipschitz-continuously on its label within each block on which the initial laws and the graphon are Lipschitz. In the proof of Theorem 4.2 it controls the replacement of $\mu_{v,s}$ by $\mu_{\lceil nv\rceil/n,s}$.
--
--   **Formalization Note** The paper states Theorem 2.1 for (2.1) under Condition 2.1, and p. 3597 says it still holds for (4.2), "a special case of (2.1)", with Remark 5.2 allowing $\varepsilon=0$ when $b,\sigma$ are bounded. Accordingly Condition 4.1(a)–(c) stands in for Condition 2.1 here; Condition 4.1(d) concerns $\beta_n$ and is irrelevant to (4.2). $W_{2,T}$ takes values in $[0,\infty]$.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3593, Theorem 2.1(b); for (4.2): p. 3597, after (4.2), and Remark 5.2, p. 3604

import Mathlib
import Definitions.Def_GraphonMF_SparseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.SparseRate

/-- Theorem 2.1(b) (p. 3593) for the limit system (4.2) under Conditions 4.1(a)–(c) and 2.3:
`W_{2,T}(μ_u, μ_v) ≤ κ|u − v|` whenever `u, v` lie in one interval `J_i` of Condition 2.3. -/
theorem theorem_2_1_b {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (h41a : Cond41a μ0) (h41b : Cond41b b) (h41c : Cond41c σ)
    {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G) {N : ℕ} {J : Fin N → Set I} (h23 : Cond23 μ0 G J)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ i : Fin N, ∀ u ∈ J i, ∀ v ∈ J i,
      GraphonMF.DenseRate.W2T (P.map (GraphonMF.DenseRate.pathOf T (X u))) (P.map (GraphonMF.DenseRate.pathOf T (X v))) ≤
        ENNReal.ofReal (κ * |(u : ℝ) - v|) := by sorry

end GraphonMF.SparseRate
