-- Prove2me | Theorems.Thm_GlobalTheory_HeckeOne_extensionEmbedding_mixedSymm_of_isReal
-- name    : GlobalTheory.HeckeOne.extensionEmbedding_mixedSymm_of_isReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:23.839804+00:00
-- url     : https://prove2.me/theorems/0885cd68-f69f-4d50-9901-d8ac1b3d0728
-- title:
--   Hecke One: extension Embedding mixed Symm of is Real
-- statement:
--   The Hecke One construction uses the extension Embedding mixed Symm of is Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExtensionEmbeddingMixedSymmOfIsComplex.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExtensionEmbeddingMixedSymmOfIsComplex.lean#L39-L42

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

theorem GlobalTheory.HeckeOne.extensionEmbedding_mixedSymm_of_isReal (y : mixedSpace K) (v : InfinitePlace K) (hv : v.IsReal) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.1 ⟨v, hv⟩ := by sorry
