-- Prove2me | Theorems.Thm_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam
-- name    : MvFormalGroup.BigWittLaw.subst_artinHasse_frobFam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/2ed93fdd-5b73-56c7-a534-215ca3ae7c87
-- title:
--   Artin–Hasse coordinates intertwine the big Witt and Witt Frobenii
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure, and let $m$ be a natural number. Three $\mathbb{N}$-indexed families of power series enter. First, for each $k$, [`MvFormalGroup.ArtinHasse.coord p k`](def/MvFormalGroup_ArtinHasse.html#L103) is the polynomial in $\mathbb{Z}_p[X_0,\dots,X_k]$ obtained as the coefficient of $T^{k+1}$ in the product $\prod_{j<k+1}$ `scaled` $p\,p^{j}\,X_j$ of scaled Artin–Hasse series in the tautological variables; these are pushed forward along $\mathbb{Z}_p \to R$ and viewed in `MvPowerSeries ℕ R`. Second, [`MvFormalGroup.BigWittLaw.frobFam R p m`](def/MvFormalGroup_BigWittFrobenius.html#L432) is the image in `MvPowerSeries ℕ R` of the integral polynomial `frobPoly p m`, the coefficient of $T^{m+1}$ in $\prod_{k<p(m+1)}$ `frobFactor` $p\,k$, mapped along $\mathbb{Z}\to R$. Third, [`MvFormalGroup.WittLaw.frobPolyFam p R`](def/MvFormalGroup_CartierModuleIntVerschiebung.html#L119) sends $n$ to the $n$-th coordinate of the Witt-vector Frobenius of the tautological Witt vector over $R$. The assertion is that substituting the Artin–Hasse family into the $m$-th big Witt Frobenius series equals substituting the Witt Frobenius family into the $m$-th Artin–Hasse coordinate; that is, the Artin–Hasse map commutes with the two Frobenii in coordinate $m$.
--
--   This is the coordinatewise compatibility $\mathbf{F}_p \circ \mathrm{AH} = \mathrm{AH} \circ F$ between the Frobenius of the big Witt formal group and the Witt-vector Frobenius, transported through the Artin–Hasse map, over a $\mathbb{Z}_p$-algebra. It is used in the Cartier-theoretic argument showing that a homomorphism from the big Witt formal group with vanishing tangent map is divisible by the integral Verschiebung, via [`MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam.lean

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

theorem MvFormalGroup.BigWittLaw.subst_artinHasse_frobFam
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R] (m : ℕ) :
    MvPowerSeries.subst
        (fun k => (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p k)) : MvPowerSeries ℕ R))
        (MvFormalGroup.BigWittLaw.frobFam R p m)
      = MvPowerSeries.subst (MvFormalGroup.WittLaw.frobPolyFam p R)
          (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p m)) : MvPowerSeries ℕ R) := by sorry
