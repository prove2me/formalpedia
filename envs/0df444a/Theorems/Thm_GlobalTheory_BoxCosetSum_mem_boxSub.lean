-- Prove2me | Theorems.Thm_GlobalTheory_BoxCosetSum_mem_boxSub
-- name    : GlobalTheory.BoxCosetSum.mem_boxSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:18.45348+00:00
-- url     : https://prove2.me/theorems/a11d1369-08da-4083-a421-5146e78e42fa
-- title:
--   Box Coset Sum: mem box Sub
-- statement:
--   The Box Coset Sum construction uses the mem box Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean#L66-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalingOpenSubgroupsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.BoxCosetSum
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.BoxCosetSum.mem_boxSub {κ : Type} {B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)}
    {u : κ → FiniteAdeleRing (𝓞 F) F} :
    u ∈ boxSub κ B ↔ ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v := by sorry
