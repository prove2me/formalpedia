-- Prove2me | Theorems.Thm_HunterPDE_Regularity_weakDeriv_diffQuot_comm
-- name    : HunterPDE.Regularity.weakDeriv_diffQuot_comm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:23:14.713729+00:00
-- url     : https://prove2.me/theorems/1bc35783-ac21-40f7-b109-1259107e9ae5
-- title:
--   Proposition 4.52 (1) — difference quotients commute with weak derivatives
-- statement:
--   Let $u \in L^1_{\mathrm{loc}}(\mathbb{R}^n)$ have a weak partial derivative $\partial_i u \in L^1_{\mathrm{loc}}(\mathbb{R}^n)$, and let $h \ne 0$. Then for every direction $j$ the difference quotient $D_j^h u$ is weakly differentiable in the $i$th direction, with
--   $$\partial_i D_j^h u = D_j^h \partial_i u .$$
--
--   This is the first of the elementary properties of difference quotients used to transfer the weak formulation of an elliptic equation to difference quotients of the solution.
--
--   **Formalization Note.** Coordinates are 0-based. "$g$ is a weak $\partial_i$ of $u$ on $\mathbb{R}^n$" is `HasWeakDeriv Set.univ (Pi.single i 1) u g`, which includes local integrability of $u$ and $g$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 124, Proposition 4.52 (1)

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_HunterPDE_Regularity_DiffQuotient

namespace HunterPDE.Regularity

/-- Proposition 4.52 (1) of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 124 (commutativity of
difference quotients with weak derivatives): if `u, ∂ᵢu ∈ L¹_loc(ℝⁿ)`, then
`∂ᵢ D_j^h u = D_j^h ∂ᵢ u`. Here `g` is a weak `i`th partial derivative of `u` on `ℝⁿ`
(`HasWeakDeriv Set.univ (Pi.single i 1) u g`, which includes `u, g ∈ L¹_loc(ℝⁿ)`), and the
conclusion is that `D_j^h g` is a weak `i`th partial derivative of `D_j^h u` on `ℝⁿ`. The size
`h` is nonzero as in Definition 4.51. Coordinates are 0-based. -/
theorem weakDeriv_diffQuot_comm {n : ℕ} (i j : Fin n) (h : ℝ) (hh : h ≠ 0)
    (u g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Shared.HasWeakDeriv Set.univ (Pi.single i 1) u g) :
    Shared.HasWeakDeriv Set.univ (Pi.single i 1) (diffQuot j h u) (diffQuot j h g) := by sorry

end HunterPDE.Regularity
