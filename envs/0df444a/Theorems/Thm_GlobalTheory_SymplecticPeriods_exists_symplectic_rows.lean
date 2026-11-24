-- Prove2me | Theorems.Thm_GlobalTheory_SymplecticPeriods_exists_symplectic_rows
-- name    : GlobalTheory.SymplecticPeriods.exists_symplectic_rows
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:25:14.934355+00:00
-- url     : https://prove2.me/theorems/d464ae3c-8ed8-4d55-b561-2046adb488c2
-- title:
--   Symplectic Periods: exists symplectic rows
-- statement:
--   The Symplectic Periods construction uses the exists symplectic rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsSymplecticActionOfPeriodLatticeMap.lean#L11-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsSymplecticActionOfPeriodLatticeMap.lean#L11-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsSymplecticActionOfPeriodLatticeMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SymplecticPeriods
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.SymplecticPeriods.exists_symplectic_rows (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ j,
      F (fun i => σ j (Sum.inr i), fun i => σ j (Sum.inl i)) =
        (fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inr i),
          fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inl i)) := by sorry
