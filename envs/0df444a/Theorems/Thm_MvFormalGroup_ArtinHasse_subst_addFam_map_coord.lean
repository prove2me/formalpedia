-- Prove2me | Theorems.Thm_MvFormalGroup_ArtinHasse_subst_addFam_map_coord
-- name    : MvFormalGroup.ArtinHasse.subst_addFam_map_coord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/a47cc02e-34a6-54b9-989e-7f369a6b9de8
-- title:
--   Artin–Hasse coordinates are additive over a ℤₚ-algebra
-- statement:
--   Fix a natural number $p$ that is prime, a commutative ring $R$ equipped with an algebra structure over $\mathbb{Z}_p$, and a natural number $n$. Write $h_n :=$ [`MvFormalGroup.ArtinHasse.coord p n`](def/MvFormalGroup_ArtinHasse.html#L103), the polynomial in $\mathbb{Z}_p[X_0, X_1, \dots]$ obtained as the coefficient of degree $n+1$ of the product $\prod_{m < n+1}$ `scaled p (p ^ m) (X m)`, and let $h_n^R$ denote its image in $R[X_0,X_1,\dots]$ under $\mathbb{Z}_p \to R$, viewed as an element of `MvPowerSeries ℕ R`. The assertion is an identity between two elements of `MvPowerSeries (Fin 2 × ℕ) R`. On the left, the variables of $h_n^R$ are substituted by the family [`MvFormalGroup.WittLaw.addFam p R`](def/MvFormalGroup_CartierModule.html#L107), whose $m$-th member is the image over $R$ of the Witt addition polynomial `WittVector.wittAdd p m` in the two blocks of variables $X_{0,\bullet}$, $X_{1,\bullet}$. On the right, one substitutes into the image over $R$ of the polynomial $X_{0,n} + X_{1,n} + \sum_{i<n} X_{0,i} X_{1,n-1-i}$ (the $n$-th big Witt addition law [`MvFormalGroup.BigWittLaw.addFam R n`](def/MvFormalGroup_BigWittLaw.html#L67)) the family [`MvFormalGroup.WittLaw.pairFam`](def/MvFormalGroup_CartierModule.html#L341) attached to $m \mapsto h_m^R$, which sends a pair $(i,m)$ to $h_m^R$ with its variables relabelled by `blk i` into the $i$-th block.
--
--   This is the statement that the Artin–Hasse map, with coordinates $h_n$, is a homomorphism from the $p$-typical Witt formal group to the big Witt formal group (the multiplicative group $1 + tR[[t]]$) over an arbitrary $\mathbb{Z}_p$-algebra, rather than only over rings of characteristic $p$. It feeds the construction of the factors of the Cartier splitting in [`MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt) and the related statements on Verschiebung and on truncated generating series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_ArtinHasse_subst_addFam_map_coord.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_ArtinHasse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.ArtinHasse.subst_addFam_map_coord
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R] (n : ℕ) :
    MvPowerSeries.subst (MvFormalGroup.WittLaw.addFam p R)
        (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p n)) : MvPowerSeries ℕ R) =
      MvPowerSeries.subst
        (MvFormalGroup.WittLaw.pairFam fun m =>
          (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p m)) : MvPowerSeries ℕ R))
        (MvFormalGroup.BigWittLaw.addFam R n) := by sorry
