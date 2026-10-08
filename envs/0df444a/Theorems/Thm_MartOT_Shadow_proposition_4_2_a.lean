-- Prove2me | Theorems.Thm_MartOT_Shadow_proposition_4_2_a
-- name    : MartOT.Shadow.proposition_4_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:33.75015+00:00
-- url     : https://prove2.me/theorems/8a649121-72b2-45e4-9c9a-b85f2d9eb751
-- title:
--   Proposition 4.2, first bullet, p. 21 — for µ, ν ∈ 𝓜 of equal mass, µ ⪯C ν iff u_µ ≤ u_ν
-- statement:
--   Let $\mathcal M$ be the finite Borel measures on $\mathbb R$ with finite first moment and, for $\mu\in\mathcal M$, let the **potential function** $u_\mu(x)=\int|y-x|\,d\mu(y)$. Write $\mu\preceq_C\nu$ for the convex order ($\int\varphi\,d\mu\le\int\varphi\,d\nu$ for every convex $\varphi:\mathbb R\to\mathbb R$).
--
--   Let $\mu,\nu\in\mathcal M$ have the same mass, $\mu(\mathbb R)=\nu(\mathbb R)$. Then
--   $$\mu\preceq_C\nu\iff u_\mu(x)\le u_\nu(x)\ \text{ for all }x\in\mathbb R .$$
--
--   No equality of means is assumed: it is a consequence of either side. This characterization turns convex-order statements into pointwise inequalities between convex functions, the main device of the construction of shadows.
-- source:
--   arXiv:1208.1509v2, Proposition 4.2 (first bullet), p. 21

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory

theorem proposition_4_2_a (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν)
    (hmass : μ Set.univ = ν Set.univ) :
    MartOT.Var.ConvexLE μ ν ↔ ∀ x : ℝ, MartOT.Var.potential μ x ≤ MartOT.Var.potential ν x := by sorry

end MartOT.Shadow
