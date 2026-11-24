-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_exists_isRegular_ofList_eq_maximalIdeal
-- name    : GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:08.787323+00:00
-- url     : https://prove2.me/theorems/c33ed30f-8e33-4f2f-a318-56e264d6423c
-- title:
--   Scheme Coh: exists is Regular of List eq maximal Ideal
-- statement:
--   The Scheme Coh construction uses the exists is Regular of List eq maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean#L13-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean#L13-L80

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal RingTheory.Sequence
universe u
variable {R : Type u} [CommRing R]

theorem GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal [IsRegularLocalRing R] :
    ∃ rs : List R, IsRegular R rs ∧ ofList rs = maximalIdeal R ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim R := by sorry
