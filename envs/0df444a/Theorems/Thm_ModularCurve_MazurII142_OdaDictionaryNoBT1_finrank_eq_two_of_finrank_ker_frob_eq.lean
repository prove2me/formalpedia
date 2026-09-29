-- Prove2me | Theorems.Thm_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq
-- name    : ModularCurve.MazurII142.OdaDictionaryNoBT1.finrank_eq_two_of_finrank_ker_frob_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/1ab6fe3c-96da-533a-9fff-dbece80253c1
-- title:
--   Multiplicity one for J[𝔪] from an Oda packet
-- statement:
--   Let $\mathbb T$ be a commutative ring, $J$ a $\mathbb T$-module, $\mathfrak m\subset\mathbb T$ a maximal ideal, so that $k=\mathbb T/\mathfrak m$ is a field, and let $Vrep$, $HDR$, $MV$, $H0\Omega$, $H1O$ be $k$-vector spaces. Let $P$ be a datum of type `MazurII142.OdaDictionaryNoBT1`, that is: endomorphism pairs $(F,V)$ on $HDR$ and on $MV$ (written `P.DHDR` and `P.DMV`), each satisfying $V\circ F=0$ and $F\circ V=0$; $k$-linear isomorphisms $H0\Omega\cong\ker(F_{HDR})$ and $H1O\cong HDR/\operatorname{im}(V_{HDR})$; a surjective $k$-linear map $\pi\colon HDR\to MV$ with $\pi\circ V_{HDR}=V_{MV}\circ\pi$ and $\pi\circ F_{HDR}=F_{MV}\circ\pi$; and the rank ties $\dim_k J[\mathfrak m]=\dim_k HDR$ and $\dim_k Vrep=\dim_k MV$, where $J[\mathfrak m]=\operatorname{torsionBySet}_{\mathbb T}(J,\mathfrak m)$. Assume $HDR$ is finite-dimensional over $k$; that $\dim_k\ker(F_{MV})=\dim_k\bigl(MV/\operatorname{im}(V_{MV})\bigr)$; the clause `P.FontaineLayer`, namely that if $\ker\pi$ is nontrivial then there is a subspace $N\subseteq\ker\pi$ stable under the restrictions of $F_{HDR}$ and $V_{HDR}$ to $\ker\pi$ together with a $k$-linear isomorphism $e\colon(\ker\pi)/N\to MV$ carrying the induced $V$ on $(\ker\pi)/N$ to $V_{MV}$; that $\dim_k H1O\le 1$; and that $\dim_k Vrep=2$. Then $\dim_k J[\mathfrak m]=2$.
--
--   This is the linear-algebra engine behind Mazur's multiplicity-one statement for the $\mathfrak m$-torsion of a Jacobian in the first of his two cases, with the Dieudonné-module input packaged as an abstract Oda dictionary and self-duality replaced by the single numerical hypothesis $\dim\ker F=\dim\operatorname{coker}V$ on $MV$. It is used in the proof of [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem), the bound on the Hecke $\mathfrak m$-torsion of $J_0$ attached to an absolutely irreducible residual representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.lean

import Mathlib
import Definitions.Def_HeckeGalois_MazurCase1BundleNoBT1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w
set_option autoImplicit false
attribute [local instance] Ideal.Quotient.field in
open ModularCurve in

theorem ModularCurve.MazurII142.OdaDictionaryNoBT1.finrank_eq_two_of_finrank_ker_frob_eq
    {𝕋 : Type u} [CommRing 𝕋] {J : Type v} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋} [𝔪.IsMaximal]
    {Vrep : Type w} [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
    {HDR : Type w} [AddCommGroup HDR] [Module (𝕋 ⧸ 𝔪) HDR]
    {MV : Type w} [AddCommGroup MV] [Module (𝕋 ⧸ 𝔪) MV]
    {H0Ω : Type w} [AddCommGroup H0Ω] [Module (𝕋 ⧸ 𝔪) H0Ω]
    {H1O : Type w} [AddCommGroup H1O] [Module (𝕋 ⧸ 𝔪) H1O]
    (P : MazurII142.OdaDictionaryNoBT1 𝕋 J 𝔪 (𝕋 ⧸ 𝔪) Vrep HDR MV H0Ω H1O)
    [FiniteDimensional (𝕋 ⧸ 𝔪) HDR]
    (hrank : Module.finrank (𝕋 ⧸ 𝔪) ↥(LinearMap.ker P.DMV.frob) =
      Module.finrank (𝕋 ⧸ 𝔪) (MV ⧸ LinearMap.range P.DMV.ver))
    (hlayer : P.FontaineLayer)
    (h94 : Module.finrank (𝕋 ⧸ 𝔪) H1O ≤ 1)
    (hdimV : Module.finrank (𝕋 ⧸ 𝔪) Vrep = 2) :
    Module.finrank (𝕋 ⧸ 𝔪) ↥(Submodule.torsionBySet 𝕋 J 𝔪) = 2 := by sorry
