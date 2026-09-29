-- Prove2me | Theorems.Thm_MvFormalGroup_BigWittLaw_subst_addFam_projFam_and_subst_artinHasse_projFam
-- name    : MvFormalGroup.BigWittLaw.subst_addFam_projFam_and_subst_artinHasse_projFam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/38b6c01e-dbfd-5866-88f6-6988fd11fcb4
-- title:
--   Additivity of `projFam` and splitting of Artin–Hasse
-- statement:
--   Let $p$ be a prime and let $R$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure. Write $\pi_k :=$ [`MvFormalGroup.BigWittLaw.projFam R p k`](def/MvFormalGroup_BigWittFrobenius.html#L434), the image in `MvPowerSeries ℕ R` of the integral polynomial `wittCoord (p ^ k - 1)` in variables indexed by $\mathbb{N}$, and let [`MvFormalGroup.BigWittLaw.addFam R n`](def/MvFormalGroup_BigWittLaw.html#L67) be the image in `MvPowerSeries (Fin 2 × ℕ) R` of $X_{(0,n)} + X_{(1,n)} + \sum_{i<n} X_{(0,i)}X_{(1,n-1-i)}$, while [`MvFormalGroup.WittLaw.addFam p R k`](def/MvFormalGroup_CartierModule.html#L107) is the image in `MvPowerSeries (Fin 2 × ℕ) R` of the Witt addition polynomial `WittVector.wittAdd p k`. The theorem asserts the conjunction of two families of identities. First, for every $k$, substituting the family `addFam R` into $\pi_k$ gives the same power series as substituting the family [`MvFormalGroup.WittLaw.pairFam (projFam R p)`](def/MvFormalGroup_CartierModule.html#L341), whose value at $(i,n)$ is $\pi_n$ with its variables relabelled into the $i$-th block via `blk i`, into `WittLaw.addFam p R k`. Second, for every $k$, substituting into $\pi_k$ the family indexed by $i$ whose $i$-th member is the image in `MvPowerSeries ℕ R` of [`MvFormalGroup.ArtinHasse.coord p i`](def/MvFormalGroup_ArtinHasse.html#L103) under $\mathbb{Z}_p \to R$ — that is, the coefficient of degree $i+1$ of $\prod_{m<i+1}$ `scaled p (p ^ m) (X m)` — yields exactly the variable $X_k$.
--
--   This is Cartier's $p$-typification: the explicit projector from the big Witt formal group to the $p$-typical Witt formal group is a homomorphism of formal group laws, and it is a left inverse of the Artin–Hasse map. It is used in the construction of integral Verschiebung operators on Cartier modules, via [`MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_BigWittLaw_subst_addFam_projFam_and_subst_artinHasse_projFam.lean

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

theorem MvFormalGroup.BigWittLaw.subst_addFam_projFam_and_subst_artinHasse_projFam
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R] :
    (∀ k : ℕ, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (MvFormalGroup.BigWittLaw.projFam R p k) =
      MvPowerSeries.subst
        (MvFormalGroup.WittLaw.pairFam (MvFormalGroup.BigWittLaw.projFam R p))
        (MvFormalGroup.WittLaw.addFam p R k)) ∧
    (∀ k : ℕ, MvPowerSeries.subst
        (fun i => (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p i)) : MvPowerSeries ℕ R))
        (MvFormalGroup.BigWittLaw.projFam R p k) = MvPowerSeries.X k) := by sorry
