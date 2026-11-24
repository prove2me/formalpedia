-- Prove2me | Theorems.Thm_GlobalTheory_ProjModFinIso_finrank_prod_eq
-- name    : GlobalTheory.ProjModFinIso.finrank_prod_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:04.374745+00:00
-- url     : https://prove2.me/theorems/cc16cd0c-9bda-46ab-a00a-6bb8f537a142
-- title:
--   Proj Mod Fin Iso: finrank prod eq
-- statement:
--   The Proj Mod Fin Iso construction uses the finrank prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L9-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem GlobalTheory.ProjModFinIso.finrank_prod_eq (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R (M × N) = Module.finrank R M + Module.finrank R N := by sorry
