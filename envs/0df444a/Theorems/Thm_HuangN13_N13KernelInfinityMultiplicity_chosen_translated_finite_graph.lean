-- Prove2me | Theorems.Thm_HuangN13_N13KernelInfinityMultiplicity_chosen_translated_finite_graph
-- name    : HuangN13.N13KernelInfinityMultiplicity.chosen_translated_finite_graph
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:30:46.624275+00:00
-- url     : https://prove2.me/theorems/8eff9ed5-7ede-4428-ac3e-cc87226ee969
-- title:
--   chosen translated finite graph
-- statement:
--   Exact transplant of the original proof of MazurProof.N13KernelInfinityMultiplicity.chosen_translated_finite_graph from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines4389–4400, command SHA-256 51df456c40d3b870b4fe27a931a58fa805502320066a26867a4eebe32008787a.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_CompatibleReductionCore
import Definitions.Def_HuangN13_DegreeFourStatementCore
import Definitions.Def_HuangN13_DoublingStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13KernelInfinityMultiplicity.chosen_translated_finite_graph (z : MazurProof.N13KernelBaseDivisor.Kernel) :
    ∃ E : MazurProof.N13Mumford.SemiMumford MazurProof.N13TwoChartPicardRealization.Q₂,
      MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E ∧ E.u.natDegree = 2 ∧ E.nInf = -1 ∧
      MazurProof.N13TwoChartPicardRealization.genericRaw (MazurProof.N13CalibratedChooser.choose ((z : MazurProof.N13ConstructedSpecialization.G) +
          MazurProof.N13KernelBaseDivisor.baseTranslate)).charts
        (MazurProof.N13CalibratedChooser.choose ((z : MazurProof.N13ConstructedSpecialization.G) +
          MazurProof.N13KernelBaseDivisor.baseTranslate)).infinityOrder = MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated
        (MazurProof.N13CalibratedChooser.choose ((z : MazurProof.N13ConstructedSpecialization.G) +
          MazurProof.N13KernelBaseDivisor.baseTranslate)).charts := by sorry
