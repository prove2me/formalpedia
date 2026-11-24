-- Prove2me | Theorems.Thm_GlobalTheory_ClassWeight_exists_proj
-- name    : GlobalTheory.ClassWeight.exists_proj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:14:34.163943+00:00
-- url     : https://prove2.me/theorems/750dea11-b490-4f93-933f-72c4676e1543
-- title:
--   Class Weight: exists proj
-- statement:
--   The Class Weight construction uses the exists proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean#L65-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean#L65-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ClassSubStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassWeight
variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}
variable {E : Type} [AddCommGroup E] [Module F E] {W : X → Type} [∀ α, AddCommGroup (W α)] [∀ α, Module F (W α)]

theorem GlobalTheory.ClassWeight.exists_proj [Module.Finite ℤ X] [IsAlgClosed F] (hN : (N : F) ≠ 0) (S : ∀ α, E →ₗ[F] W α)
    (hc : (Nat.card (TorChar X F N) : F) ≠ 0) (l : TorChar X F N → E → E)
    (hl : ∀ τ v β, S β (l τ v) = (evalChar F N β τ : F) • S β v) (α : X) (v : E) :
    ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v := by sorry
