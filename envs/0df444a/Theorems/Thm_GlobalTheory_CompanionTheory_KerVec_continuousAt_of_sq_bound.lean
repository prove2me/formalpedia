-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerVec_continuousAt_of_sq_bound
-- name    : GlobalTheory.CompanionTheory.KerVec.continuousAt_of_sq_bound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:50.725413+00:00
-- url     : https://prove2.me/theorems/8b28f80a-cee4-4f34-9e6b-8045591bd1f1
-- title:
--   Ker Vec: continuous At of sq bound
-- statement:
--   The Ker Vec construction uses the continuous At of sq bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousAtOfSqBound.lean#L20-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousAtOfSqBound.lean#L20-L43

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousAtOfSqBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerVec

theorem GlobalTheory.CompanionTheory.KerVec.continuousAt_of_sq_bound {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SeminormedAddCommGroup E] (f : G → E) (y₀ : G) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ w in 𝓝 (1 : G),
      ‖f (y₀ * w) - f y₀‖ₑ ^ 2 ≤ c * ENNReal.ofReal ε ^ 2) : ContinuousAt f y₀ := by sorry
