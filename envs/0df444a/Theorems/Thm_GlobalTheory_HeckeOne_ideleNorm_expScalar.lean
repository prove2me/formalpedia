-- Prove2me | Theorems.Thm_GlobalTheory_HeckeOne_ideleNorm_expScalar
-- name    : GlobalTheory.HeckeOne.ideleNorm_expScalar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:13.923122+00:00
-- url     : https://prove2.me/theorems/4479737e-6f7c-44c1-abf9-c9df03b94b8f
-- title:
--   Hecke One: idele Norm exp Scalar
-- statement:
--   The Hecke One construction uses the idele Norm exp Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExtensionEmbeddingMixedSymmOfIsComplex.lean#L88-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExtensionEmbeddingMixedSymmOfIsComplex.lean#L88-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExtensionEmbeddingMixedSymmOfIsComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable (K : Type) [Field K] [NumberField K]

theorem GlobalTheory.HeckeOne.ideleNorm_expScalar (x : ℝ) :
    ideleNorm (mixedIdele K (expScalar K x)) = Real.exp ((Module.finrank ℚ K : ℝ) * x) := by sorry
