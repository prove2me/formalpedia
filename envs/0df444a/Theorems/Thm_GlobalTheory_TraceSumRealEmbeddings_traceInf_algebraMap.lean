-- Prove2me | Theorems.Thm_GlobalTheory_TraceSumRealEmbeddings_traceInf_algebraMap
-- name    : GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:01.523426+00:00
-- url     : https://prove2.me/theorems/6a8f6d73-6c3f-4661-86fe-c7ce22447108
-- title:
--   Trace Sum Real Embeddings: trace Inf algebra Map
-- statement:
--   The Trace Sum Real Embeddings construction uses the trace Inf algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TraceInfAlgebraMap.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TraceInfAlgebraMap.lean#L29-L36

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TraceInfAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceSumRealEmbeddings
open NumberField NumberField.InfinitePlace

theorem GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf F (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) x) =
      ((Algebra.trace ℚ F x : ℚ) : ℝ) := by sorry
