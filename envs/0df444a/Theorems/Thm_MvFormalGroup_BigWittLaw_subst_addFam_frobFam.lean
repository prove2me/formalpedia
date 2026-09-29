-- Prove2me | Theorems.Thm_MvFormalGroup_BigWittLaw_subst_addFam_frobFam
-- name    : MvFormalGroup.BigWittLaw.subst_addFam_frobFam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/4f1f3170-17d8-5a73-a20a-e4e3e293a675
-- title:
--   Frobenius family mathbf Fₙ is additive for the big Witt law
-- statement:
--   Fix a commutative ring $R$, a natural number $n$ with $0<n$, and a natural number $m$. Two elements of $\mathrm{MvPowerSeries}\,(\mathrm{Fin}\,2\times\mathbb N)\,R$ are asserted to be equal. On one side, the $m$-th member of the big Witt Frobenius family [`MvFormalGroup.BigWittLaw.frobFam R n`](def/MvFormalGroup_BigWittFrobenius.html#L432) — the image in $R$-coefficients of the integral polynomial [`MvFormalGroup.BigWittLaw.frobPoly n m`](def/MvFormalGroup_BigWittFrobenius.html#L221), namely the coefficient of degree $m+1$ of the product $\prod_{k<n(m+1)}$ of the factors `frobFactor n k` — has its variables, indexed by $\mathbb N$, substituted by the big Witt addition family [`MvFormalGroup.BigWittLaw.addFam R`](def/MvFormalGroup_BigWittLaw.html#L67), whose $j$-th member is the polynomial $X_{(0,j)}+X_{(1,j)}+\sum_{i<j}X_{(0,i)}X_{(1,j-1-i)}$ read over $R$. On the other side, the $m$-th addition polynomial [`MvFormalGroup.BigWittLaw.addFam R m`](def/MvFormalGroup_BigWittLaw.html#L67) has each of its variables $(i,j)\in\mathrm{Fin}\,2\times\mathbb N$ substituted by [`MvFormalGroup.WittLaw.pairFam`](def/MvFormalGroup_CartierModule.html#L341) of the Frobenius family at $(i,j)$, i.e. by the series obtained from the $j$-th Frobenius member by the substitution `blk i` carrying the variables indexed by $\mathbb N$ into those indexed by $\mathrm{Fin}\,2\times\mathbb N$.
--
--   This is the coordinatewise additivity of the $n$-th Frobenius family for the big Witt formal group law: $\mathbf F_n(\Sigma(a;b))=\Sigma(\mathbf F_n a;\mathbf F_n b)$, so that $\mathbf F_n$ is an endomorphism of that formal group. It is used in the Cartier-module development, in particular by [`MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_BigWittLaw_subst_addFam_frobFam.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.subst_addFam_frobFam
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (m : ℕ) :
    MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (MvFormalGroup.BigWittLaw.frobFam R n m) =
      MvPowerSeries.subst
        (MvFormalGroup.WittLaw.pairFam (MvFormalGroup.BigWittLaw.frobFam R n))
        (MvFormalGroup.BigWittLaw.addFam R m) := by sorry
