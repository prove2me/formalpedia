-- Prove2me | Theorems.Thm_MazurTransfer_original_bialgebra_base_change_point_restriction_laws
-- name    : MazurTransfer.original_bialgebra_base_change_point_restriction_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-22T02:19:52.900058+00:00
-- url     : https://prove2.me/theorems/f7de634f-6a6c-4d65-9c22-7a981f893a77
-- statement:
--   The canonical scalar change of the same given genuine bialgebra map has its original pure-tensor formula and preserves the original arithmetic point restriction square over every original coefficient algebra. Both complete original propositions and helper types, the original scalar-change constructor type and whole value, and both original point restriction types and whole values are independently checked. Every original commutative ring, Hopf algebra, bialgebra map, coefficient algebra and scalar tower hypothesis is retained. Named downstream consumer: normalized literal mu19 realization of the previously selected integral pi quotient after canonical scalar change at nineteen.

import Definitions.Def_MazurTransfer_OriginalBialgebraBaseChangePointRestrictionData20261020
import Definitions.Def_MazurTransfer_OriginalHopfBaseChangeArithmeticPointsData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraPointRestrictionData20261020
noncomputable section
open MazurTransfer
open MazurTransfer.BialgebraBaseChangePointRestriction
open scoped TensorProduct

theorem MazurTransfer.original_bialgebra_base_change_point_restriction_laws : (∀ {R S H G : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H] [CommRing G] [HopfAlgebra R G], ∀ (j : H →ₐc[R] G) (s : S) (h : H),
baseChangeMap (S := S) j (s ⊗ₜ[R] h) = s ⊗ₜ[R] j h) ∧ (∀ {R S H G : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H] [CommRing G] [HopfAlgebra R G], ∀ {K : Type} [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K], ∀ (j : H →ₐc[R] G)
    (f : WithConv (S ⊗[R] G →ₐ[S] K)),
HopfBaseChangeArithmeticPoints.restrictPoint
        (BialgebraPointRestriction.restrictPoint (baseChangeMap (S := S) j) f) =
      BialgebraPointRestriction.restrictPoint j
        (HopfBaseChangeArithmeticPoints.restrictPoint f)) := by sorry
