-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAlg_hk_alg
-- name    : GlobalTheory.CompanionTheory.HeckeAlg.hk_alg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:31.139207+00:00
-- url     : https://prove2.me/theorems/51c66cfa-2969-4259-a011-a79d1fa94414
-- title:
--   Hecke Alg: hk alg
-- statement:
--   The Hecke Alg construction uses the hk alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeAlgebraStructure.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeAlgebraStructure.lean#L11-L20

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HkMemFixed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOutNeZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeAlgebraStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeAlg

theorem GlobalTheory.CompanionTheory.HeckeAlg.hk_alg : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by sorry
