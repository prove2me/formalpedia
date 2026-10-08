-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_theorem_2_1_a
-- name    : GraphonMF.DenseLLN.theorem_2_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:38.412111+00:00
-- url     : https://prove2.me/theorems/b609202a-e107-4a91-8067-3b6a83dc982e
-- title:
--   Theorem 2.1(a), p. 3593 — under Condition 2.2, u ↦ μ_u is W_{2,T}-continuous on each interval I_i
-- statement:
--   Assume Condition 2.1 and Condition 2.2 for a finite cover $I_1,\dots,I_N$ of $I$, let $G$ be a graphon, and let $X=(X_u)_{u\in I}$ solve the graphon particle system (2.1), with path laws $\mu_u=\mathcal L(X_u)\in\mathcal P(\mathcal C_d)$. Then for each $i\in\{1,\dots,N\}$ the map $I_i\ni u\mapsto\mu_u$ is continuous for $W_{2,T}$: for every $u\in I_i$ and every sequence $u_k\in I_i$ with $u_k\to u$,
--   $$W_{2,T}(\mu_{u_k},\mu_u)\longrightarrow0 .$$
--
--   This is the continuity half of the paper's first main result. The proofs of Lemma 6.1 (through (6.10)) and Lemma 6.2 use it.
--
--   **Formalization Note** Continuity on $I_i$ is stated in its sequential form (equivalent on the metric space $I_i$), because $W_{2,T}$ takes values in $[0,\infty]$. Condition 2.2 is assumed in full (parts (a) and (b), same intervals), as the theorem says.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3593, Theorem 2.1(a)

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem theorem_2_1_a {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d N : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (hT : 0 < T)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (h21 : GraphonMF.Stability.Cond21 ε μ0 b σ)
    (J : Fin N → Set GraphonMF.Stability.I) (h22a : Cond22a μ0 J)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G) (h22b : Cond22b G J)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (hX : IsGraphonSolution noise G b σ X) :
    ∀ i, ∀ u ∈ J i, ∀ us : ℕ → GraphonMF.Stability.I, (∀ k, us k ∈ J i) → Tendsto us atTop (𝓝 u) →
      Tendsto (fun k => GraphonMF.Stability.W2T (GraphonMF.Stability.law P X (us k)) (GraphonMF.Stability.law P X u)) atTop (𝓝 0) := by sorry
end GraphonMF.DenseLLN
