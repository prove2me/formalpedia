-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_epi_of_nonempty
-- name    : GlobalTheory.OnePoint.epi_of_nonempty
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:37:49.966486+00:00
-- url     : https://prove2.me/theorems/b26a8ab4-8b9b-4174-a713-c426917018b5
-- title:
--   One Point: epi of nonempty
-- statement:
--   The One Point construction uses the epi of nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L143-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L143-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]

theorem GlobalTheory.OnePoint.epi_of_nonempty {T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K)) : Epi g := by sorry
