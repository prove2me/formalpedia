-- Prove2me | Theorems.Thm_GlobalTheory_ChF_mem_sup_span_X_pow_iff_and_isAdicComplete
-- name    : GlobalTheory.ChF.mem_sup_span_X_pow_iff_and_isAdicComplete
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:15.130917+00:00
-- url     : https://prove2.me/theorems/bc15432d-afd9-45fe-9d92-2bd23c8a1ec2
-- title:
--   Ch F: mem sup span X pow iff and is Adic Complete
-- statement:
--   The Ch F construction uses the mem sup span X pow iff and is Adic Complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemSupSpanXPowIffAndIsAdicComplete.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemSupSpanXPowIffAndIsAdicComplete.lean#L64-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemSupSpanXPowIffAndIsAdicComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ChF
open MvPowerSeries

theorem GlobalTheory.ChF.mem_sup_span_X_pow_iff_and_isAdicComplete : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : Type) [Finite κ], (∀ (n : ℕ) (f : MvPowerSeries κ R), f ∈ (I.map (MvPowerSeries.C : R →+* MvPowerSeries κ R) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R))) ^ n ↔ ∀ e : κ →₀ ℕ, MvPowerSeries.coeff e f ∈ I ^ (n - e.degree)) ∧ (IsAdicComplete I R → IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries κ R) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R)) := by sorry
