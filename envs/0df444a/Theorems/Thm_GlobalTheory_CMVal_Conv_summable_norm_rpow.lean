-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Conv_summable_norm_rpow
-- name    : GlobalTheory.CMVal.Conv.summable_norm_rpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:17.971628+00:00
-- url     : https://prove2.me/theorems/3e2f337b-352a-467a-a5b1-31f5c7431fc4
-- title:
--   Conv: summable norm rpow
-- statement:
--   The Conv construction uses the summable norm rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIntegersOfMemHatO.lean#L51-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIntegersOfMemHatO.lean#L51-L95

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntegersOfMemHatO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Conv
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Conv.summable_norm_rpow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ) (t : ℝ), c ≠ ⊥ → 1 < t → Summable fun q : modUnits (lattice c y) => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-t) := by sorry
