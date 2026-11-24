-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_incl_mem_iff
-- name    : GlobalTheory.CompanionTheory.TfLoc.Iw.incl_mem_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:56.160714+00:00
-- url     : https://prove2.me/theorems/911e13f0-7fa9-4457-9f78-2ef319e1df61
-- title:
--   Iw: incl mem iff
-- statement:
--   The Iw construction uses the incl mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L272-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L272-L282

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [FiniteDimensional k E]

theorem GlobalTheory.CompanionTheory.TfLoc.Iw.incl_mem_iff {n : ℕ} (g : GL (Fin n) k) :
    incl g ∈ iwahori (m := n) E ↔ g ∈ iwahori (m := n) k := by sorry
