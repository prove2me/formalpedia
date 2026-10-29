-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_rightPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
-- name    : LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.rightPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T15:22:13.474539+00:00
-- url     : https://prove2.me/theorems/d653e42a-f051-404a-a051-353f17397b66
-- title:
--   Right Placed Projectivization Repair Of Source Almost Projective Two Mul
-- statement:
--   **An almost-projective right measurement can be repaired locally.**
--
--   Let $\psi$ be a normalized quantum state on $H_A\otimes H_B$, let $B=\{B_a\}$ be a complete measurement on $H_B$, and let $\zeta\ge0$. Suppose the state-weighted source defect of its right lift is at most $2\zeta$:
--
--   $$
--   \sum_a \operatorname{ev}_{\psi}\!\left(\widehat B_a-\widehat B_a^2\right)\le2\zeta,
--   \qquad \widehat B_a=I_{H_A}\otimes B_a.
--   $$
--
--   Then there exists a projective submeasurement $P$ on $H_B$ such that the constant families of the right-placed submeasurements $B$ and $P$ satisfy
--
--   $$
--   \operatorname{SDDRel}_{\psi,\mathcal U_1}
--    \bigl(B^{\mathrm R},P^{\mathrm R};\,84\,\zeta^{1/4}\bigr).
--   $$
--
--   Here $\mathcal U_1$ is the uniform distribution on a singleton question set. The repair preserves locality, and the explicit error is the definition `orthonormalizationMainLemmaError(\zeta)=84\zeta^{1/4}`. This is the right-register projectivization step used by the heterogeneous Bob-side orthonormalization theorem.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.MakingMeasurementsProjective.rightPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean#L583-L726

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

open LIDT
/-!
# Section 5 — Locality-preserving projectivization repair

This file proves the locality-preserving repair route for the late Section 5
`Q/X/XHat/P` argument.

## Scope

The **spectral-truncation stage** (the first part of the proof of rounding
to projectors) is already proved by
`spectralTruncationStatement_of_sourceAlmostProjective` in
`MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean`,
which is fully proved via
`projectiveNonMeasurement_of_sourceAlmostProjective_full`. Proofs that
require the spectral truncation statement should call that declaration directly.

The main result recorded here:

- **`leftLiftedProjectivizationRepair`** — paper origin
  `references/ldt-paper/orthonormalization.tex` lines 534–860 (rank
  reduction and the `Q`/`√Q` completeness setup) and 862–1194 (the
  `X`/`X̂`/`P` algebra producing the lifted projective sub-measurement,
  including the final triangle-inequality assembly).  The formal proof below
  follows that local `Q/X/XHat/P` route by passing to the left marginal state,
  constructing the local projective family there, and transporting the final
  estimate back to left lifts.

The theorem proved here is the direct output of that route under a normalized
bipartite state and the source almost-projective estimate for the left-lifted
measurement. It is stated directly in terms of this estimate, rather than in
terms of a separate repair-input assumption, and provides the unconditional
repair step used by the orthonormalization theorem.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

theorem LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.rightPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (B : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ιB) (ζ : _root_.LIDT.MIPStarRE.LDT.Error) (hζ : 0 ≤ ζ)
    (hsource :
      ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
        ((_root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B).outcome a -
          (_root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B).outcome a *
            (_root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B).outcome a) ≤ 2 * ζ) :
    ∃ P : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas Outcome ιB,
      _root_.LIDT.MIPStarRE.LDT.SDDRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) P.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemmaError ζ) := by sorry
