-- Prove2me | Theorems.Thm_GlobalTheory_CapelliCentral_eabEnd_apply
-- name    : GlobalTheory.CapelliCentral.eabEnd_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:33:54.254518+00:00
-- url     : https://prove2.me/theorems/f87fab1c-9f53-433b-b994-9a8b03755d0f
-- title:
--   Capelli Central: eab End apply
-- statement:
--   The Capelli Central construction uses the eab End apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SmoothAddSmul.lean#L198-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SmoothAddSmul.lean#L198-L207

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
open Matrix
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.CapelliCentral.eabEnd_apply (a b : Fin n) (F : _root_.GlobalTheory.CapelliCentral.smoothSpace ε E)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, _root_.Formalism.REAL.inUJ ε g → F.1 g = f g)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) :
    (_root_.GlobalTheory.CapelliCentral.eabEnd ε E a b F).1 g = _root_.Formalism.REAL.EabV ε a b f g := by sorry
