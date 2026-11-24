-- Prove2me | Theorems.Thm_GlobalTheory_SatakeBound_eq_of_hermMat_eq
-- name    : GlobalTheory.SatakeBound.eq_of_hermMat_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:25.455902+00:00
-- url     : https://prove2.me/theorems/d6b8a3ae-be3f-4252-8a4a-92ef9ae1e4fc
-- title:
--   Satake Bound: eq of herm Mat eq
-- statement:
--   The Satake Bound construction uses the eq of herm Mat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PowDvdOfHermMatEq.lean#L67-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PowDvdOfHermMatEq.lean#L67-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermiteReductionUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open GlobalTheory GlobalTheory.SatakeBound
variable {R : Type} [CommRing R] {n : ℕ}
variable {p : R} {a a' : Fin n → ℕ}
variable [IsDomain R]

theorem GlobalTheory.SatakeBound.eq_of_hermMat_eq (hp : p ≠ 0) {c c' : HermIdx p a} {W : Matrix (Fin n) (Fin n) R}
    (h : hermMat p a c = hermMat p a c' * W) : c = c' := by sorry
