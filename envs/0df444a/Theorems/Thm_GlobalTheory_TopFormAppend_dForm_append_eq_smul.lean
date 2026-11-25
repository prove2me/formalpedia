-- Prove2me | Theorems.Thm_GlobalTheory_TopFormAppend_dForm_append_eq_smul
-- name    : GlobalTheory.TopFormAppend.dForm_append_eq_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:41.308832+00:00
-- url     : https://prove2.me/theorems/54ff0642-836f-4a68-8119-95f09c484a7f
-- title:
--   Top Form Append: d Form append eq smul
-- statement:
--   The Top Form Append construction uses the d Form append eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KaehlerWedgeFormMapEqSmulOfBasis.lean#L10-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KaehlerWedgeFormMapEqSmulOfBasis.lean#L10-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KaehlerWedgeFormMapEqSmulOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct
set_option autoImplicit false
open GlobalTheory GlobalTheory.TopFormAppend

theorem GlobalTheory.TopFormAppend.dForm_append_eq_smul : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by sorry
