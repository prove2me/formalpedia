-- Prove2me | Theorems.Thm_GlobalTheory_NormSheaf_map_normForm_eq_prod
-- name    : GlobalTheory.NormSheaf.map_normForm_eq_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:36:15.075808+00:00
-- url     : https://prove2.me/theorems/917e555c-0ab6-4772-ad55-e06a11f96233
-- title:
--   Norm Sheaf: map norm Form eq prod
-- statement:
--   The Norm Sheaf construction uses the map norm Form eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteAlgebraSplittingNormForm.lean#L10-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteAlgebraSplittingNormForm.lean#L10-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteAlgebraSplittingNormForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.NormSheaf

theorem GlobalTheory.NormSheaf.map_normForm_eq_prod (K L Ω : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Field Ω] [Algebra K Ω] (e : Fin (Module.finrank K L) ≃ (L →ₐ[K] Ω)) {m : ℕ} (x : Fin m → L) :
    (normForm K L x).map (algebraMap K Ω) = ∏ j, ∑ i, C (e j (x i)) * X i := by sorry
