-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FormalClosed_eq_bot_of_forall_mem_zeroLocusOpen
-- name    : GlobalTheory.CompanionTheory.FormalClosed.eq_bot_of_forall_mem_zeroLocusOpen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:10:01.626582+00:00
-- url     : https://prove2.me/theorems/eb686194-1584-4899-a503-2a2c4973eb09
-- title:
--   Formal Closed: eq bot of forall mem zero Locus Open
-- statement:
--   The Formal Closed construction uses the eq bot of forall mem zero Locus Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsIsoOfIsClosedImmersionOfThickenings.lean#L34-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsIsoOfIsClosedImmersionOfThickenings.lean#L34-L53

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_FormalAlgebraisation_GEClosedProj
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsIsoOfIsClosedImmersionOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FormalClosed
open GlobalTheory.ThickeningClosed

theorem GlobalTheory.CompanionTheory.FormalClosed.eq_bot_of_forall_mem_zeroLocusOpen {X : Scheme.{0}} (K : X.IdealSheafData)
    (h : ∀ x, x ∈ zeroLocusOpen K) : K = ⊥ := by sorry
