-- Prove2me | Theorems.Thm_MvFormalGroup_BigWittLaw_subst_pow_subst_projFam
-- name    : MvFormalGroup.BigWittLaw.subst_pow_subst_projFam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/96b5e8a2-bc86-5b45-bfb3-c742cb67392d
-- title:
--   The ω-curve of f∘π is the standard curve of f
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring, and let $f \in R[[X_0, X_1, \dots]]$ be a power series in variables indexed by $\mathbb{N}$ whose constant coefficient vanishes. Write [`MvFormalGroup.BigWittLaw.projFam R p`](def/MvFormalGroup_BigWittFrobenius.html#L434) for the family of power series indexed by $k \in \mathbb{N}$ whose $k$-th member is the image in $R[[X_0, X_1, \dots]]$, under the coefficientwise map induced by $\mathbb{Z} \to R$, of the integral polynomial `wittCoord (p ^ k - 1)`, and [`MvFormalGroup.CartierModule.curveFam R`](def/MvFormalGroup_CartierModule.html#L1071) for the family of one-variable series over $R$ given by $X$ in index $0$ and $0$ in every index $k+1$. The assertion is that substituting the family `projFam R p` into $f$ and then substituting, for the variable with index $m$, the power $X^{m+1} \in R[[X]]$, gives the same element of $R[[X]]$ as substituting the family `curveFam R` into $f$ directly; that is, $(f \circ \pi)(t, t^2, t^3, \dots) = f(t, 0, 0, \dots)$.
--
--   This reconciles the two parametrisations of curves used on the Cartier-theoretic side: the $\omega$-convention, in which a homomorphism out of the big formal group is evaluated at $(t, t^2, t^3, \dots)$, and the standard curve $(t, 0, 0, \dots)$ attached to a power series in the Witt variables. It is used in the construction of an integral Verschiebung representative for a Cartier-module element with vanishing tangent map over a $\mathbb{Z}_p$-algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_BigWittLaw_subst_pow_subst_projFam.lean

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

theorem MvFormalGroup.BigWittLaw.subst_pow_subst_projFam
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (f : MvPowerSeries ℕ R)
    (hf0 : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1))
        (MvPowerSeries.subst (MvFormalGroup.BigWittLaw.projFam R p) f)
      = MvPowerSeries.subst (MvFormalGroup.CartierModule.curveFam R) f := by sorry
