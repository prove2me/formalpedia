-- Prove2me | Theorems.Thm_MvFormalGroup_BigWittLaw_exists_hom_subst_pow_eq
-- name    : MvFormalGroup.BigWittLaw.exists_hom_subst_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/44a9d314-eb7f-52cc-95b0-ff3a161c7aec
-- title:
--   Cartier's first theorem, ω-curve form
-- statement:
--   Let $R$ be a commutative ring, $d$ a natural number and $\Phi$ a $d$-dimensional formal group law over $R$: a $d$-tuple $\Phi_1,\dots,\Phi_d$ of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with zero constant terms, whose linear parts are $X_{\mathrm{inl}\,i} + X_{\mathrm{inr}\,i}$, and which is associative in the usual substitution sense; assume $\Phi$ commutative, i.e. interchanging the two blocks of variables fixes every component. Let $\gamma : \mathrm{Fin}\,d \to R[[t]]$ be power series with zero constant coefficients. Then there is a $d$-tuple $G$ of power series in countably many variables $a_0,a_1,\dots$ over $R$, each with zero constant coefficient, such that: substituting into $G_j$ the big Witt addition family, whose $n$-th member is the image in $R$ of $X_{(0,n)} + X_{(1,n)} + \sum_{i<n} X_{(0,i)}X_{(1,n-1-i)}$, gives the same result as substituting into $\Phi_j$ the pair of tuples obtained from $G$ by renaming the $m$-th variable to $X_{(0,m)}$ respectively $X_{(1,m)}$; and substituting $t^{m+1}$ for the $m$-th variable of $G_j$ gives $\gamma_j$.
--
--   This is Cartier's first theorem in its $\omega$-curve form: every curve on a commutative formal group law $\Phi$ arises, by evaluation at $(t,t^2,t^3,\dots)$, from a homomorphism of the big Witt formal group law into $\Phi$. It is obtained from the variant recording the value on the family [`MvFormalGroup.CartierModule.curveFam`](def/MvFormalGroup_CartierModule.html#L1071), and is used in the construction of integral Verschiebung operators for formal groups with vanishing tangent condition over $\mathbb{Z}_p$-algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_BigWittLaw_exists_hom_subst_pow_eq.lean

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

theorem MvFormalGroup.BigWittLaw.exists_hom_subst_pow_eq
    {R : Type u} [CommRing R] {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (γ : Fin d → PowerSeries R) (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) :
    ∃ G : Fin d → MvPowerSeries ℕ R,
      (∀ j, MvPowerSeries.constantCoeff (G j) = 0) ∧
      (∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
          MvPowerSeries.subst
            (Sum.elim
              (fun l => MvPowerSeries.subst
                (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
              fun l => MvPowerSeries.subst
                (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
            (Φ.toPowerSeries j)) ∧
      (∀ j, MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j) = γ j) := by sorry
