-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_isMulRightInvariant_map
-- name    : GlobalTheory.SmGL.UnipHaar.isMulRightInvariant_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:14:12.92992+00:00
-- url     : https://prove2.me/theorems/c51c6f37-e45a-4a4d-95af-3a3e85de2dca
-- title:
--   Unip Haar: is Mul Right Invariant map
-- statement:
--   The Unip Haar construction uses the is Mul Right Invariant map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarIsMulRightInvariant.lean#L48-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarIsMulRightInvariant.lean#L48-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarIsMulRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.SmGL.UnipHaar.isMulRightInvariant_map :
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν)).IsMulRightInvariant := by sorry
