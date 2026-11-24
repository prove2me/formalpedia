-- Prove2me | Theorems.Thm_GlobalTheory_NotLeSqSup_main
-- name    : GlobalTheory.NotLeSqSup.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:47.532888+00:00
-- url     : https://prove2.me/theorems/c13db6ec-d2bd-499f-95ec-5df02d8f82f3
-- title:
--   Not Le Sq Sup: main
-- statement:
--   The Not Le Sq Sup construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotLeSqSup.lean#L25-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotLeSqSup.lean#L25-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotLeSqSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NotLeSqSup

theorem GlobalTheory.NotLeSqSup.main : ∀ {k A : Type} [inst : Field k] [inst_1 : CommRing A] [inst_2 : Algebra k A] (aug : A →ₐ[k] k) {I : Ideal A} {n : ℕ}, RingHom.ker aug ^ (n + (1 : ℕ)) = ⊥ → I ≤ RingHom.ker aug → ¬RingHom.ker aug ≤ I → ∃ (φ : A →ₐ[k] DualNumber k), AlgHom.comp (TrivSqZeroExt.fstHom k k k) φ = aug ∧ (∀ a ∈ I, (φ : A → DualNumber k) a = (0 : DualNumber k)) ∧ ∃ a ∈ RingHom.ker aug, (φ : A → DualNumber k) a ≠ (0 : DualNumber k) := by sorry
