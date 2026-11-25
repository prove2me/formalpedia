-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatStruct_finite_field_invol
-- name    : GlobalTheory.MaxLatStruct.finite_field_invol
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:30.590293+00:00
-- url     : https://prove2.me/theorems/0bfbfef0-66b0-4b90-ac42-bd6419473f50
-- title:
--   Max Lat Struct: finite field invol
-- statement:
--   The Max Lat Struct construction uses the finite field invol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L14-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L14-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct

theorem GlobalTheory.MaxLatStruct.finite_field_invol {k : Type*} [Field k] [Finite k] (τ : k →+* k) (hτ : ∀ a, τ (τ a) = a)
    (θ : k) (hθ : θ - τ θ ≠ 0) :
    (∃ q : ℕ, 2 ≤ q ∧ Nat.card k = q ^ 2) ∧ ∀ u, τ u = u → ∃ w, τ w * w = u := by sorry
