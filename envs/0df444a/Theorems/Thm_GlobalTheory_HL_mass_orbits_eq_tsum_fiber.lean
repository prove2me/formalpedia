-- Prove2me | Theorems.Thm_GlobalTheory_HL_mass_orbits_eq_tsum_fiber
-- name    : GlobalTheory.HL.mass_orbits_eq_tsum_fiber
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:36:11.570193+00:00
-- url     : https://prove2.me/theorems/452dcdd5-f1cd-4d37-9b9e-df28a9e8b93d
-- title:
--   HL: mass orbits eq tsum fiber
-- statement:
--   The HL construction uses the mass orbits eq tsum fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MassOrbitsEqTsumFiber.lean#L55-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MassOrbitsEqTsumFiber.lean#L55-L123

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.mass_orbits_eq_tsum_fiber : ∀ {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y] (H K0 : Subgroup G) (P : X → Prop) (π : X → Y), K0 ≤ H → (∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x ∧ invVol K0 (H ⊓ MulAction.stabilizer G (h • x)) = invVol K0 (H ⊓ MulAction.stabilizer G x)) → (∀ x, P x → K0.relIndex (H ⊓ MulAction.stabilizer G x) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G x).relIndex K0 ≠ 0 ∧ K0.relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G (π x)).relIndex K0 ≠ 0) → (∑' o : MulAction.orbitRel.Quotient H X, if P o.out then ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G o.out)) else 0) = ∑' c : MulAction.orbitRel.Quotient H Y, ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G c.out)) * (({x | P x ∧ π x = c.out} : Set X).encard : ℝ≥0∞) := by sorry
