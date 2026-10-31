-- Prove2me | Theorems.Thm_HuangN13_N13MarkedTensorComparison_exists_integral_tensor_comparison
-- name    : HuangN13.N13MarkedTensorComparison.exists_integral_tensor_comparison
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:14:03.920039+00:00
-- url     : https://prove2.me/theorems/66bd3365-d4aa-4eb6-9d9a-f6de4ef2c1d5
-- title:
--   Construct the actual integral tensor comparison
-- statement:
--   Extract the common generic multiplier from the equality of Picard classes. Choose primitive affine and infinity numerators for that same multiplier. The affine cleared equation, the two oriented branch ideal equations, and the integral infinity descent give both chart ideal equations. The original common-presentation identity supplies their single overlap equation, completing the integral comparison record.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines2689–2764, command SHA-256 344902d84d681dd0ac6ef3c5234ba6a32a437485ef164b0250d304f337205ccb.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MarkedTensorComparison.exists_integral_tensor_comparison
    (E₀ E₁ E₂ E₃ : MazurProof.N13Mumford.SemiMumford MazurProof.N13OverlapBranchCompatibility.Q₂)
    (h₀ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₀) (h₁ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₁)
    (h₂ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₂) (h₃ : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E₃)
    (D₀ D₁ D₂ D₃ : MazurProof.N13TwoChartPicardRealization.Data)
    (hraw₀ : MazurProof.N13TwoChartPicardRealization.genericRaw D₀.charts D₀.infinityOrder = MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E₀)
    (hraw₁ : MazurProof.N13TwoChartPicardRealization.genericRaw D₁.charts D₁.infinityOrder = MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E₁)
    (hraw₂ : MazurProof.N13TwoChartPicardRealization.genericRaw D₂.charts D₂.infinityOrder = MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E₂)
    (hraw₃ : MazurProof.N13TwoChartPicardRealization.genericRaw D₃.charts D₃.infinityOrder = MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E₃)
    (hs₀ : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated D₀.charts) (hs₁ : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated D₁.charts)
    (hs₂ : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated D₂.charts) (hs₃ : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated D₃.charts)
    (hm₀ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities D₀.charts (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₀) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₀))
    (hm₁ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities D₁.charts (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₁) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₁))
    (hm₂ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities D₂.charts (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₂) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₂))
    (hm₃ : MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities D₃.charts (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E₃) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E₃))
    (hclass : D₀.toGenericPic + D₁.toGenericPic = D₂.toGenericPic + D₃.toGenericPic) :
    Nonempty (MazurProof.N13CoherentChartComparison.IntegralComparison
      (MazurProof.N13MarkedTensorComparison.tensor D₀.charts D₁.charts) (MazurProof.N13MarkedTensorComparison.tensor D₂.charts D₃.charts)) := by sorry
