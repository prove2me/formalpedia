-- Prove2me | Theorems.Thm_IsLocalRing_isAdicComplete_map_maximalIdeal_quotient
-- name    : IsLocalRing.isAdicComplete_map_maximalIdeal_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/986966b7-bf77-5580-9d8b-014fbba0f3d0
-- title:
--   Adic completeness passes to quotients of a complete local ring
-- statement:
--   Let $R$ be a commutative ring which is local and Noetherian, and assume $R$ is adically complete for its maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R`, i.e. the canonical map to the $\mathfrak m$-adic limit is both injective (Hausdorff: an element congruent to $0$ modulo $\mathfrak m^n\cdot\top$ for all $n$ is $0$) and surjective (precomplete: every sequence that is Cauchy for the filtration by the submodules $\mathfrak m^n\cdot\top$ has a limit). Let $J \subseteq R$ be an arbitrary ideal, with no condition relating $J$ to $\mathfrak m$ and in particular $J = R$ allowed. The conclusion is that the quotient ring $R/J$ is adically complete for the ideal $\mathfrak m\,(R/J)$, the image of $\mathfrak m$ under the quotient map `Ideal.Quotient.mk J`; that is, $R/J$ satisfies both the Hausdorff and the precompleteness conditions for the filtration by powers of that image ideal. Note that the ideal appearing in the conclusion is described as the image of $\mathfrak m$, not as the maximal ideal of $R/J$ (the two agree when $J \neq R$).
--
--   This is the standard fact that adic completeness descends to quotients, in the form needed to keep track of completeness when passing from a ring such as $\mathcal O[[X_1,\dots,X_n]]$, or from a deformation ring, to a quotient by an arbitrary ideal. It is used in the study of deformation rings and their presentations, for instance in the identification of the kernel of an algebra homomorphism with an explicit span of relations and in the criterion for bijectivity via the length of the cotangent module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isAdicComplete_map_maximalIdeal_quotient.lean

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem IsLocalRing.isAdicComplete_map_maximalIdeal_quotient {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (J : Ideal R) : IsAdicComplete ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J)) (R ⧸ J) := by sorry
