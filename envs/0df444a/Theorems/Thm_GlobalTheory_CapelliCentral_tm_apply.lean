-- Prove2me | Theorems.Thm_GlobalTheory_CapelliCentral_tm_apply
-- name    : GlobalTheory.CapelliCentral.tm_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:34:16.823463+00:00
-- url     : https://prove2.me/theorems/ae60de24-234d-43db-93ab-e617bc64354f
-- title:
--   Capelli Central: tm apply
-- statement:
--   The Capelli Central construction uses the tm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SmoothAddSmul.lean#L231-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SmoothAddSmul.lean#L231-L236

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SmoothAddSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CapelliCentral
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.CapelliCentral.tm_apply (u : ℂ) (a b : Fin n) (F : smoothSpace ε E) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (h : ∀ g, inUJ ε g → F.1 g = f g) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    (Tm (eabEnd ε E) u a b F).1 g = Top (EabV ε) u a b f g := by sorry
