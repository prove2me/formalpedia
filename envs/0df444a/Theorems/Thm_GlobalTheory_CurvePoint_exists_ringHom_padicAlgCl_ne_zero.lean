-- Prove2me | Theorems.Thm_GlobalTheory_CurvePoint_exists_ringHom_padicAlgCl_ne_zero
-- name    : GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:29:58.140309+00:00
-- url     : https://prove2.me/theorems/45eb7f0d-6efe-4236-b7b1-edc051ba08b1
-- title:
--   Curve Point: exists ring Hom padic Alg Cl ne zero
-- statement:
--   The Curve Point construction uses the exists ring Hom padic Alg Cl ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomPadicAlgClNeZero.lean#L10-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomPadicAlgClNeZero.lean#L10-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeNotMemForallGtEqMaximalIdealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOneOfFinitePadicIntDomainStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePadicIntDomainEmbeddingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomPadicAlgClNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CurvePoint

theorem GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by sorry
