-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_eq_of_monic_aeval_eq_zero_map_residue_eq_pow
-- name    : IsDiscreteValuationRing.eq_of_monic_aeval_eq_zero_map_residue_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/9bb4365c-2d89-5a4a-b6ec-41c99feda051
-- title:
--   Uniqueness of the residual value of an element
-- statement:
--   Let $\mathcal O$ be a commutative domain which is a discrete valuation ring, with residue field $k=\mathrm{ResidueField}\,\mathcal O$ and reduction map $\mathrm{residue}\,\mathcal O\colon\mathcal O\to k$, and let $F$ be a field which is an $\mathcal O$-algebra whose structure map $\mathcal O\to F$ is injective. Let $x\in F$ and let $c,c'\in k$. Suppose given a monic $R\in\mathcal O[X]$ with $R(x)=0$ (in the sense that the $\mathcal O$-algebra evaluation `aeval x R` vanishes) whose reduction satisfies $\bar R=(X-C\,c)^{\deg R}$ in $k[X]$, the exponent being the natural degree of $R$, and a monic $R'\in\mathcal O[X]$ with $R'(x)=0$ whose reduction satisfies $\bar R'=(X-C\,c')^{\deg R'}$. The conclusion is that $c=c'$. Thus an element of $F$ can be "residually $c$" for at most one $c\in k$, where being residually $c$ is the polynomial condition just described, which requires no residue map on $F$ itself.
--
--   This is the well-definedness of the residual value of an element of a field extension integral over a discrete valuation ring, a polynomial substitute for reduction that makes sense in, say, an algebraic closure of $\mathrm{Frac}\,\mathcal O$ where no residue map exists. It is used in the Hecke-algebra arguments for newforms, where the residues of the eigenvalues $\theta(U_q)$ must be matched with values predicted on the Galois side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_eq_of_monic_aeval_eq_zero_map_residue_eq_pow.lean

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem IsDiscreteValuationRing.eq_of_monic_aeval_eq_zero_map_residue_eq_pow
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {F : Type} [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F))
    (x : F) (c c' : IsLocalRing.ResidueField 𝒪)
    (R : Polynomial 𝒪) (hR : R.Monic) (hRx : Polynomial.aeval x R = 0)
    (hRc : R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c) ^ R.natDegree)
    (R' : Polynomial 𝒪) (hR' : R'.Monic) (hR'x : Polynomial.aeval x R' = 0)
    (hR'c : R'.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c') ^ R'.natDegree) :
    c = c' := by sorry
