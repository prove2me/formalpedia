-- Prove2me | Theorems.Thm_GlobalTheory_HaarLatticeScale_measureReal_valued_le_exp
-- name    : GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:31.604994+00:00
-- url     : https://prove2.me/theorems/3a4001b4-a6f8-4656-98b1-476cb736efe3
-- title:
--   Haar Lattice Scale: measure Real valued le exp
-- statement:
--   The Haar Lattice Scale construction uses the measure Real valued le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MeasureRealValuedLeExp.lean#L78-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MeasureRealValuedLeExp.lean#L78-L95

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsResidueEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MeasureRealValuedLeExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.HaarLatticeScale

theorem GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (e : V ≃L[Fv F v] (ι → Fv F v)) (n : ℤ), μ.real {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp n} = ((Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ^ n) ^ Fintype.card ι * μ.real {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} := by sorry
