-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Calc_isU_tv
-- name    : GlobalTheory.UTrans.Calc.isU_tv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:20:40.561642+00:00
-- url     : https://prove2.me/theorems/336f16cb-a880-4d1b-b831-e5bc99fcea35
-- title:
--   Calc: is U tv
-- statement:
--   The Calc construction uses the is U tv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TransvectionIdentitiesUnitary.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TransvectionIdentitiesUnitary.lean#L68-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Calc
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

theorem GlobalTheory.UTrans.Calc.isU_tv (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x : Fin n → R) (t : R)
    (h : t + σ t + t * σ t * hf σ G x x = 0) : IsU σ G (tv σ G x t) := by sorry
