-- Prove2me | Theorems.Thm_GlobalTheory_local_norm_of_ideal_norm
-- name    : GlobalTheory.local_norm_of_ideal_norm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:08:54.532055+00:00
-- url     : https://prove2.me/theorems/3c7cf295-42c2-496b-93c6-ac12f942a6d2
-- title:
--   Global Theory: local norm of ideal norm
-- statement:
--   The Global Theory construction uses the local norm of ideal norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L346-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L346-L362

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open LocalNorm

theorem GlobalTheory.local_norm_of_ideal_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (x : maximalRealSubfield E), x ≠ 0 → (∃ I J : Ideal (𝓞 E), I ≠ ⊥ ∧ J ≠ ⊥ ∧ FractionalIdeal.spanSingleton (𝓞 E)⁰ ((x : E)) * ((I * I.map (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = ((J * J.map (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ a b : v.adicCompletion (maximalRealSubfield E), algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) x = a ^ 2 - algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) (-(H.d : maximalRealSubfield E)) * b ^ 2) := by sorry
