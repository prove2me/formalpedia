-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBaseChangeAt_of_isAffineOpen
-- name    : GroundTheory.Arith.SchemeCoh.isBaseChangeAt_of_isAffineOpen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:05.921546+00:00
-- url     : https://prove2.me/theorems/b13a36ab-93c3-4cc3-9b78-c18729042301
-- title:
--   Scheme Coh: is Base Change At of is Affine Open
-- statement:
--   The Scheme Coh construction uses the is Base Change At of is Affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L212-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L212-L224

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {W T U : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.isBaseChangeAt_of_isAffineOpen (g : T ⟶ U) (N : U.Modules) [N.IsQuasicoherent]
    {V : U.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen (g ⁻¹ᵁ V)) :
    IsBaseChangeAt g N V := by sorry
