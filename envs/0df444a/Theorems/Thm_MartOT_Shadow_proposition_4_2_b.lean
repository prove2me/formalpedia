-- Prove2me | Theorems.Thm_MartOT_Shadow_proposition_4_2_b
-- name    : MartOT.Shadow.proposition_4_2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:28.293052+00:00
-- url     : https://prove2.me/theorems/17a7bdf9-1a06-45b9-8744-7e6e0d282764
-- title:
--   Proposition 4.2, second bullet, p. 21 — for µ, ν ∈ 𝓜, µ ≤ ν iff u_ν − u_µ is convex
-- statement:
--   Let $\mu,\nu$ be finite Borel measures on $\mathbb R$ with finite first moment and let the **potential function** $u_\mu(x)=\int|y-x|\,d\mu(y)$. Then
--   $$\mu\le\nu\iff u_\nu-u_\mu\ \text{ is convex on }\mathbb R,$$
--   where $\mu\le\nu$ means $\mu(A)\le\nu(A)$ for every Borel set $A$. In words, $u_\mu$ has smaller curvature than $u_\nu$.
--
--   This translates the domination constraint $\eta\le\nu$ in the definition of the shadow into a concavity condition on potential functions.
-- source:
--   arXiv:1208.1509v2, Proposition 4.2 (second bullet), p. 21

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory

theorem proposition_4_2_b (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) :
    μ ≤ ν ↔ ConvexOn ℝ Set.univ (fun x : ℝ => MartOT.Var.potential ν x - MartOT.Var.potential μ x) := by sorry

end MartOT.Shadow
