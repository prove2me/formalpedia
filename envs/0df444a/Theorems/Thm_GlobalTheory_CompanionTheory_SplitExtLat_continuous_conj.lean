-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_continuous_conj
-- name    : GlobalTheory.CompanionTheory.SplitExtLat.continuous_conj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:15:04.404541+00:00
-- url     : https://prove2.me/theorems/965fa30c-158c-4281-86ba-dca1eba88eaa
-- title:
--   Split Ext Lat: continuous conj
-- statement:
--   The Split Ext Lat construction uses the continuous conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitHomeoApply.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitHomeoApply.lean#L47-L51

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitExtLat
variable {P G₁ : Type} [Group P] [Group G₁]

theorem GlobalTheory.CompanionTheory.SplitExtLat.continuous_conj [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) :
    Continuous fun z : G₁ × π.ker => MulAut.conjNormal (ι z.1) z.2 := by sorry
