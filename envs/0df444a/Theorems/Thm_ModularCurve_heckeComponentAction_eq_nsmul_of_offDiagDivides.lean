-- Prove2me | Theorems.Thm_ModularCurve_heckeComponentAction_eq_nsmul_of_offDiagDivides
-- name    : ModularCurve.heckeComponentAction_eq_nsmul_of_offDiagDivides
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/9f6d4198-62d6-5b38-bca2-81105191a6d0
-- title:
--   Hecke action on the component group is multiplication by n
-- statement:
--   Let $\iota$ be a finite index set with decidable equality, let $e:\iota\to\mathbb{N}$ be a family of widths, let $B$ be an $\iota\times\iota$ matrix of integers and let $n\in\mathbb{Z}$. Assume: $e(x)>0$ for every $x$; `HeckeRowSums B n`, i.e. $\sum_{j}B_{ij}=n$ for every $i$; `HeckeWeightSymm e B`, i.e. $e_j B_{ij}=e_i B_{ji}$ for all $i,j$; and `HeckeOffDiagDivides e B`, i.e. $e_i \mid B_{ij}$ whenever $i\neq j$. Here the character lattice `characterLattice ι` is the kernel of the linear map `degreeOn ι` on $\iota\to\mathbb{Z}$, and the component group `componentGroup e` is the quotient of the $\mathbb{Z}$-dual of that lattice by the image of `gramMap e`, the restriction of the pairing `widthPairing e` to the character lattice regarded as a map into its dual. By the row-sum hypothesis the endomorphism `heckeDivisorAction B` preserves the character lattice, and its dual map descends, by the weighted symmetry hypothesis, to the endomorphism `heckeComponentAction e B hrow hsym` of `componentGroup e`. The assertion is that for every $x$ in `componentGroup e` this endomorphism sends $x$ to $n\cdot x$.
--
--   This is the combinatorial form of the statement that the Eisenstein difference $T_r-(r+1)$ annihilates the component group of a Jacobian at a bad place, as in Ribet's work on level lowering and Edixhoven's account: the three hypotheses on $B$ are those satisfied by Brandt matrices. It is used in the project to compare Hecke actions on component groups attached to places and models, and in the bounds on Hecke torsion in the component group of a Shimura-curve level datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeComponentAction_eq_nsmul_of_offDiagDivides.lean

import Definitions.Def_ModularCurve_ComponentGroupHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
namespace ModularCurve
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem heckeComponentAction_eq_nsmul_of_offDiagDivides {e : ι → ℕ} {B : Matrix ι ι ℤ}
    {n : ℤ} (he : ∀ x, 0 < e x) (hrow : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (hdiv : HeckeOffDiagDivides e B) (x : componentGroup e) :
    heckeComponentAction e B hrow hsym x = n • x := by sorry
