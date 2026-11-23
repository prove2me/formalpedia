-- Prove2me | Theorems.Thm_GlobalTheory_HeckeOne_expScalar_add
-- name    : GlobalTheory.HeckeOne.expScalar_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:54.737418+00:00
-- url     : https://prove2.me/theorems/5bcea5fc-6497-4a95-871e-b2052a1bf61b
-- title:
--   Hecke One: exp Scalar add
-- statement:
--   The Hecke One construction uses the exp Scalar add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExtensionEmbeddingMixedSymmOfIsComplex.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExtensionEmbeddingMixedSymmOfIsComplex.lean#L79-L82

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

theorem GlobalTheory.HeckeOne.expScalar_add (x y : ℝ) : expScalar K (x + y) = expScalar K x * expScalar K y := by sorry
