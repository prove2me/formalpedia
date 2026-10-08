-- Prove2me | Theorems.Thm_MartOT_Abs_stay_part_eq_inf
-- name    : MartOT.Abs.stay_part_eq_inf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:38.186696+00:00
-- url     : https://prove2.me/theorems/03476dc2-4549-4f78-ae7a-dce9e9f7692a
-- title:
--   Proof of Theorem 7.4, pp. 45–46 — an optimal plan for c = |y − x| restricted to the diagonal is (Id ⊗ Id)_#(µ ∧ ν)
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order and let $\pi$ be an optimal martingale transport plan for the cost $c(x,y)=|y-x|$. Let $\Delta=\{(x,y)\in\mathbb R^2:x=y\}$ be the diagonal. Then
--
--   $$\pi|_\Delta=(\mathrm{Id}\otimes\mathrm{Id})_\#(\mu\wedge\nu),$$
--
--   where $\mu\wedge\nu$ is the largest measure below both $\mu$ and $\nu$ and $(\mathrm{Id}\otimes\mathrm{Id})_\#\eta$ is the image of $\eta$ under $x\mapsto(x,x)$.
--
--   In words: an optimal plan for $|y-x|$ leaves in place as much mass as the marginals allow. This is the "stay" part $\pi_{\mathrm{stay}}$ of Theorem 7.4.
--
--   **Formalization Note** $\mu\wedge\nu$ is the infimum $\mu\sqcap\nu$ in Mathlib's complete lattice of measures (ordered setwise), the measure $\mu\wedge\mu'$ of Example 2.5 (p. 12); it is not a product and not a pointwise minimum of set values. The paper argues inside the proof of Theorem 7.4, whose standing hypothesis includes continuity of $\mu$; this step does not use it, so the statement is made without it.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 7.4, pp. 45–46 ("We want to prove that ρ = µ∧ν, that is, π0 is (Id⊗Id)_#(µ∧ν)" … "π0 = (Id⊗Id)_#(µ ∧ ν) as claimed above")

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem stay_part_eq_inf (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π) :
    π.restrict {p : ℝ × ℝ | p.1 = p.2} = (μ ⊓ ν).map (fun x : ℝ => (x, x)) := by sorry

end MartOT.Abs
