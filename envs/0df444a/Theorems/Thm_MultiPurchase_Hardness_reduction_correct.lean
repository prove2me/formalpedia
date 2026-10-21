-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_reduction_correct
-- name    : MultiPurchase.Hardness.reduction_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:03.213405+00:00
-- url     : https://prove2.me/theorems/beff6892-e608-459f-99fa-2b963fcc969c
-- title:
--   Proof of Theorem 1, App. p. 5 — G has a cut of size ≥ M iff the reduction instance has some C with R₂(C) ≥ 1
-- statement:
--   Let $G$ be a simple graph on $m$ nodes and $M\ge 1$ an integer. Form the BundleMVL-2 instance of the proof of Theorem 1 with threshold $\kappa=1$: products $0,1,\dots,m$, revenues $r_0=2$ and $r_i=\tfrac14-\tfrac{i}{8(m+1)}$ for $1\le i\le m$ (so $r_0>\kappa$ and $\kappa/2>r_1>\dots>r_m>0$), weights $V_{\{i\}}=\theta_{ii}=0$ and $V_{\{i,j\}}=2\theta_{ij}$ with $\theta_{ij}=q_{ij}/(r_i+r_j-\kappa)$, and no-purchase weight $v_0=M/\kappa=M$. Then
--
--   $$G\text{ has a cut with at least }M\text{ edges}\iff\text{the instance is well formed and }\max_{C}R_2(C)\ge 1 .$$
--
--   This is the correctness of the paper's reduction from Max-Cut to the decision version of the BundleMVL-2 revenue problem.
--
--   **Formalization Note** The paper leaves $\kappa$ and the revenues free subject to its inequalities; the formalization fixes the concrete values above. $M=0$ is excluded because $v_0=M/\kappa$ must be positive; every graph has a cut of size $\ge 0$, so a reduction maps $M=0$ to a fixed yes-instance.
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, proof of Theorem 1, Appendix p. 5 (PDF 37)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace MultiPurchase.Hardness

open ProjSchedTW.Complexity

/-- Proof of Theorem 1, Appendix p. 5: for every simple graph `G` on `m` nodes and every
`M ≥ 1`, `G` has a cut with at least `M` edges iff the BundleMVL-2 instance of the reduction
(`κ = 1`, `r₀ = 2`, `κ/2 > r₁ > ⋯ > r_m > 0`, `V{i} = 0`, `V{i,j} = 2θᵢⱼ`, `v0 = M/κ`) has a
recommendation set `C` with `R₂(C) ≥ κ`. -/
theorem reduction_correct {m : ℕ} (G : SimpleGraph (Fin m)) (M : ℕ) (hM : 1 ≤ M) :
    MaxCutYes G M ↔ Yes (reductionInstance G M) 1 := by sorry

end MultiPurchase.Hardness
