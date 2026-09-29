-- Prove2me | Theorems.Thm_MvFormalGroup_exists_isLawHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree_of_isComm
-- name    : MvFormalGroup.exists_isLawHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree_of_isComm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/fae7b877-aee9-5f88-add4-392fae43abec
-- title:
--   Uniqueness of the quotient by a finite formal kernel
-- statement:
--   Let $B$ be a Noetherian commutative ring, let $F,G,G'$ be commutative two-dimensional formal group laws over $B$ (objects of [`MvFormalGroup 2 B`](def/MvFormalGroup_BasicV2.html#L15), each satisfying the `IsComm` symmetry $F(y,x)=F(x,y)$), and let $\rho,\rho'$ be pairs of power series in two variables over $B$, i.e. elements of `Series B` $=$ `Fin 2 → MvPowerSeries (Fin 2) B`. Assume `IsLawHom F G ρ` and `IsLawHom F G' ρ'`: each component of $\rho$ (resp. $\rho'$) has vanishing constant term and $\rho(F(x,y))=G(\rho(x),\rho(y))$ (resp. $\rho'(F(x,y))=G'(\rho'(x),\rho'(y))$), these identities being read as substitutions into the two-variable laws. Assume further `FormalODModule.HasKernelOfDegree ρ d` for some $d\in\mathbb N$, namely that $B[\![x_1,x_2]\!]/(\rho_1,\rho_2)$ is a finite projective $B$-module whose rank after base change along any ring homomorphism $f:B\to\kappa$ into a field equals $d$, and that the two ideals $(\rho_1,\rho_2)$ and $(\rho'_1,\rho'_2)$ of $B[\![x_1,x_2]\!]$ coincide. Then there exist $u,v\in$ `Series B` with `IsLawHom G G' u` and `IsLawHom G' G v`, mutually inverse under substitution ($v\circ u=u\circ v=$ the identity pair $(x_1,x_2)$), and satisfying $u\circ\rho=\rho'$ and $v\circ\rho'=\rho$.
--
--   This is the uniqueness statement for quotients of a commutative formal group law by a finite locally free formal subgroup: two law homomorphisms out of $F$ with the same kernel ideal, one of them of finite locally free kernel of constant degree, differ by a unique isomorphism of the targets. It is used in the construction of formal coordinates on the fake elliptic curves arising in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_exists_isLawHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree_of_isComm.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem MvFormalGroup.exists_isLawHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree_of_isComm
    {B : Type} [CommRing B] [IsNoetherianRing B]
    (F G G' : MvFormalGroup 2 B) [F.IsComm] [G.IsComm] [G'.IsComm] (ρ ρ' : Series B)
    (hρ : IsLawHom F G ρ) (hρ' : IsLawHom F G' ρ')
    {d : ℕ} (hker : FormalODModule.HasKernelOfDegree ρ d)
    (hI : Ideal.span (Set.range ρ) = Ideal.span (Set.range ρ')) :
    ∃ u v : Series B, IsLawHom G G' u ∧ IsLawHom G' G v ∧
      v.comp u = Series.id B ∧ u.comp v = Series.id B ∧ u.comp ρ = ρ' ∧ v.comp ρ' = ρ := by sorry
