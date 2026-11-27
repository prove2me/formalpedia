-- Prove2me | Theorems.Thm_GlobalTheory_LocLatInert_exists_unit_of_inert
-- name    : GlobalTheory.LocLatInert.exists_unit_of_inert
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:54:21.546319+00:00
-- url     : https://prove2.me/theorems/6dafe7ef-c80b-45e3-a8da-80d9ed9c5309
-- title:
--   Loc Lat Inert: exists unit of inert
-- statement:
--   The Loc Lat Inert construction uses the exists unit of inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableLatticeEqZpowStdInertCompletion.lean#L11-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableLatticeEqZpowStdInertCompletion.lean#L11-L48

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableLatticeEqZpowStdInertCompletion
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped Matrix
open GlobalTheory GlobalTheory.LocLatInert
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.LocLatInert.exists_unit_of_inert (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (hv : ∀ x, Valued.v (σ x) = Valued.v x)
    (hx : ∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) :
    ∃ u : K, σ u * u = 1 ∧ Valued.v u ≤ 1 ∧ Valued.v (σ u) ≤ 1 ∧ 1 - u ≠ 0 ∧
      Valued.v (1 - u)⁻¹ ≤ 1 := by sorry
