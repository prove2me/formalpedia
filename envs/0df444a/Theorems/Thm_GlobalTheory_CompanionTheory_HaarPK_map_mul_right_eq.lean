-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_map_mul_right_eq
-- name    : GlobalTheory.CompanionTheory.HaarPK.map_mul_right_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:27.243071+00:00
-- url     : https://prove2.me/theorems/32ef6e0c-069d-4f7b-b438-f41248d32d58
-- title:
--   Haar PK: map mul right eq
-- statement:
--   The Haar PK construction uses the map mul right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L29-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L29-L60

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarPK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.CompanionTheory.HaarPK.map_mul_right_eq [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (hμ : μ ≠ 0) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : μ.map (fun x => x * k) = μ := by sorry
