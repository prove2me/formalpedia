-- Prove2me | Theorems.Thm_GlobalTheory_AdicCompl_v_algebraMap
-- name    : GlobalTheory.AdicCompl.v_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:41.78051+00:00
-- url     : https://prove2.me/theorems/c2b8504a-18c6-4cf5-9331-d4009706c783
-- title:
--   Adic Compl: v algebra Map
-- statement:
--   The Adic Compl construction uses the v algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NumberFieldFinitePlaceCompletionEmbedding.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NumberFieldFinitePlaceCompletionEmbedding.lean#L29-L30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open Formalism.L2.Pj Formalism.L2.PjFree
open IsDedekindDomain NumberField HeightOneSpectrum Filter
open scoped WithZero Topology
open GlobalTheory.AdicCompl
variable {R : Type} [CommRing R] [IsDedekindDomain R] {L : Type} [Field L] [Algebra R L]
  [IsFractionRing R L] (w : HeightOneSpectrum R)
local notation "Lw" => adicCompletion L w
local notation "Ow" => adicCompletionIntegers L w

theorem GlobalTheory.AdicCompl.v_algebraMap (l : L) : Valued.v (algebraMap L Lw l) = w.valuation L l := by sorry
