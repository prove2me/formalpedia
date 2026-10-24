-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_locallyLipschitz_matrixEntries_sqrt_408915f
-- name    : FunctionalInequalities.Analysis.locallyLipschitz_matrixEntries_sqrt_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:15.292991+00:00
-- url     : https://prove2.me/theorems/3b60d697-3af6-406a-aa56-2e0b04385c0d
-- title:
--   Local Lipschitz Continuity Of Matrix Square Roots
-- statement:
--   This statement establishes local Lipschitz continuity of the canonical matrix square root.
--
--   Let X be a pseudometric space, let M:X→Matrix(ι,ι,ℝ) be continuous, and assume M(x) is positive definite for every x. If the Frobenius-coordinate map
--
--   $$x\mapsto\operatorname{matrixEntries}(M(x))$$
--
--   is locally Lipschitz, then so is
--
--   $$x\mapsto\operatorname{matrixEntries}(\sqrt{M(x)}).$$
--
--   The conclusion uses the canonical functional-calculus square root and the Frobenius norm.
--
--   This result supplies a local regularity principle for positive-definite matrix profiles.
--
--   **Formalization Note** The theorem is stated for finite index types with decidable equality; positivity is pointwise positive definiteness, not merely semidefiniteness.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/InverseSqrt.lean#L162-L208 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.InverseSqrt`, declaration `FunctionalInequalities.Analysis.locallyLipschitz_matrixEntries_sqrt`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped MatrixOrder RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
section LocalLipschitz
open Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator NNReal ContDiff

theorem FunctionalInequalities.Analysis.locallyLipschitz_matrixEntries_sqrt_408915f {X : Type*} [PseudoMetricSpace X]
    (M : X → Matrix ι ι ℝ) (hM : Continuous M) (hPD : ∀ x, (M x).PosDef)
    (hInput : LocallyLipschitz (fun x => matrixEntries (M x))) :
    LocallyLipschitz (fun x => matrixEntries (CFC.sqrt (M x))) := by sorry
