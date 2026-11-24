-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_form_bijective_of_unimodular
-- name    : GlobalTheory.UnitaryStd.form_bijective_of_unimodular
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:15.900798+00:00
-- url     : https://prove2.me/theorems/ededc2e8-2bf2-448b-a951-e1d78282931d
-- title:
--   Unitary Std: form bijective of unimodular
-- statement:
--   The Unitary Std construction uses the form bijective of unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeAlternatingFormBijective.lean#L26-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeAlternatingFormBijective.lean#L26-L42

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeAlternatingFormBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.UnitaryStd

theorem GlobalTheory.UnitaryStd.form_bijective_of_unimodular : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), IsUnit S.det → Function.Bijective (GlobalTheory.UnitaryStd.form ρ g S) := by sorry
