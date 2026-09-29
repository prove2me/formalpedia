-- Prove2me | Theorems.Thm_MvFormalGroup_ArtinHasse_subst_addFam_fam
-- name    : MvFormalGroup.ArtinHasse.subst_addFam_fam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/de1fe16f-d135-5aed-bc68-76ec273b3fc9
-- title:
--   Artin–Hasse family carries Witt addition to big Witt addition
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring of characteristic $p$, and let $n$ be a natural number. Write $h_m =$ [`MvFormalGroup.ArtinHasse.fam p R m`](def/MvFormalGroup_ArtinHasse.html#L147) for the multivariate power series in the variables indexed by $\mathbb{N}$ over $R$ obtained from the polynomial [`MvFormalGroup.ArtinHasse.coord p m`](def/MvFormalGroup_ArtinHasse.html#L103) — the coefficient of $t^{m+1}$ in `prodSeries p (fun k => X k) (m+1)`, a polynomial in the variables $X_k$ over $\mathbb{Z}_p$ — by applying the ring homomorphism $\mathbb{Z}_p \to \mathbb{Z}/p \to R$ given by reduction followed by the canonical map. Write $S_m =$ [`MvFormalGroup.WittLaw.addFam p R m`](def/MvFormalGroup_CartierModule.html#L107) for the image in $R$ of the Witt addition polynomial `WittVector.wittAdd p m`, a series in the variables indexed by $\mathrm{Fin}\,2 \times \mathbb{N}$, and $\Sigma_n =$ [`MvFormalGroup.BigWittLaw.addFam R n`](def/MvFormalGroup_BigWittLaw.html#L67) for the image in $R$ of $X_{(0,n)} + X_{(1,n)} + \sum_{i<n} X_{(0,i)} X_{(1,n-1-i)}$. The assertion is the identity $$h_n(S_0, S_1, \dots) = \Sigma_n\bigl((i,m) \mapsto \text{$h_m$ in block $i$}\bigr),$$ where the left-hand side substitutes the family $(S_m)_{m}$ for the variables of $h_n$, and the right-hand side substitutes into $\Sigma_n$ the family [`MvFormalGroup.WittLaw.pairFam`](def/MvFormalGroup_CartierModule.html#L341), which sends the variable indexed by $(i,m)$ to $h_m$ with its variables relabelled by the family `blk i` attached to the block index $i$.
--
--   This is the classical statement that the Artin–Hasse map $x \mapsto \prod_{m} E_p(x_m t^{p^m})$ is a homomorphism from the $p$-typical Witt formal group to the big Witt formal group $1 + tR[[t]]$ over a ring of characteristic $p$, expressed as a coordinatewise identity between the two addition laws. It is used in the proof of [`MvFormalGroup.CartierModule.tangent_surjective`](thm.html#MvFormalGroup.CartierModule.tangent_surjective), where composing with Cartier's homomorphism attached to a curve produces $p$-typical curves with prescribed tangent vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_ArtinHasse_subst_addFam_fam.lean

import Mathlib
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_ArtinHasse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.ArtinHasse.subst_addFam_fam
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p] (n : ℕ) :
    MvPowerSeries.subst (MvFormalGroup.WittLaw.addFam p R) (MvFormalGroup.ArtinHasse.fam p R n) =
      MvPowerSeries.subst (MvFormalGroup.WittLaw.pairFam (MvFormalGroup.ArtinHasse.fam p R))
        (MvFormalGroup.BigWittLaw.addFam R n) := by sorry
