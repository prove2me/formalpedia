-- Prove2me | Theorems.Thm_HuangN13_N13PrincipalBranchIdeals_tensor_branch_ideal_equations
-- name    : HuangN13.N13PrincipalBranchIdeals.tensor_branch_ideal_equations
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:43:23.909177+00:00
-- url     : https://prove2.me/theorems/84e6189c-0927-40f8-867e-e3f15e1c152c
-- title:
--   Both tensor branch ideal equations from a primitive presentation
-- statement:
--   The primitive presentation gives the difference of the two branch orders. The principal norm identity gives their sum, so the positive orientation fixes both orders. Apply each original principal-power ideal lemma, use the corresponding expansion injectivity to preserve nonzero coefficients, and substitute the four specified infinity multiplicities. This yields the positive and negative branch ideal equations together.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines911–977, command SHA-256 332180c6c3e9c94291b4d597a76aefe5fe95bee87b35580973cc506a4cd8ee35.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13PrincipalBranchIdeals.instAlgebraAR MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13PrincipalBranchIdeals.tensor_branch_ideal_equations
    (E₀ E₁ E₂ E₃ : MazurProof.N13Mumford.SemiMumford MazurProof.N13OverlapBranchCompatibility.Q₂)
    (h₀ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₀) (h₁ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₁)
    (h₂ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₂) (h₃ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₃)
    (L₀ L₁ L₂ L₃ : MazurProof.N13TwoChartPicardRealization.Line)
    (hL₀ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities L₀ (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₀) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₀))
    (hL₁ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities L₁ (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₁) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₁))
    (hL₂ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities L₂ (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₂) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₂))
    (hL₃ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities L₃ (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₃) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₃))
    (f : MazurProof.N13PrincipalBranchIdeals.Fˣ) (n m : ℕ) (a b : MazurProof.N13OverlapBranchCompatibility.A) (c d : MazurProof.N13OverlapBranchCompatibility.B)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hf : (2 : MazurProof.N13PrincipalBranchIdeals.F) ^ m * (f : MazurProof.N13PrincipalBranchIdeals.F) * algebraMap MazurProof.N13OverlapBranchCompatibility.A MazurProof.N13PrincipalBranchIdeals.F b =
      (2 : MazurProof.N13PrincipalBranchIdeals.F) ^ n * algebraMap MazurProof.N13OverlapBranchCompatibility.A MazurProof.N13PrincipalBranchIdeals.F a)
    (hcross : MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O d =
      MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O c)
    (hprincipal :
      MazurProof.SexticMumford.mumfordIdealUnit (MazurProof.N13Mumford.model MazurProof.N13OverlapBranchCompatibility.Q₂) E₀ *
        MazurProof.SexticMumford.mumfordIdealUnit (MazurProof.N13Mumford.model MazurProof.N13OverlapBranchCompatibility.Q₂) E₁ *
        toPrincipalIdeal MazurProof.N13PrincipalBranchIdeals.R MazurProof.N13PrincipalBranchIdeals.F f =
      MazurProof.SexticMumford.mumfordIdealUnit (MazurProof.N13Mumford.model MazurProof.N13OverlapBranchCompatibility.Q₂) E₂ *
        MazurProof.SexticMumford.mumfordIdealUnit (MazurProof.N13Mumford.model MazurProof.N13OverlapBranchCompatibility.Q₂) E₃)
    (horientation : E₀.nInf + E₁.nInf +
      Multiplicative.toAdd ((MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13OverlapBranchCompatibility.Q₂).ordPlus f) =
        E₂.nInf + E₃.nInf) :
    Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion
        (Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * (L₀.infinityIdeal * L₁.infinityIdeal)) =
      Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion
        (Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * (L₂.infinityIdeal * L₃.infinityIdeal)) ∧
    Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion
        (Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * (L₀.infinityIdeal * L₁.infinityIdeal)) =
      Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion
        (Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * (L₂.infinityIdeal * L₃.infinityIdeal)) := by sorry
