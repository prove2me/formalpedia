-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_Resolvent_weighted_distance_jensen
-- name    : OAI.ThresholdParallelRepetition.Resolvent.weighted_distance_jensen
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:40:51.493545+00:00
-- url     : https://prove2.me/theorems/5486b64f-7906-4c14-a127-ce83439b8928
-- title:
--   Averaged distance of purification kernels is bounded by the Jensen gap of $A\log A$
-- statement:
--   Let $n$ be a finite index set and let $M_n(\mathbb C)$ be the complex $n\times n$ matrices. For Hermitian $X,Y$ write $X\preceq Y$ (Loewner order) if $Y-X$ is positive semidefinite. For a positive semidefinite $A$ and $s>0$ the purification kernel is
--   $$
--   K_A(s)=A\,(A+sI)^{-1},
--   $$
--   and for a positive semidefinite $A=\sum_i\lambda_iu_iu_i^*$ (spectral decomposition) let $A\log A=\sum_i\lambda_i\log\lambda_i\,u_iu_i^*$ be the functional calculus of $t\mapsto t\log t$, with $0\log0=0$.
--
--   Let $J$ be a finite index set, let $A_j\in M_n(\mathbb C)$ ($j\in J$) and $B\in M_n(\mathbb C)$ satisfy $0\preceq A_j\preceq I$ and $0\preceq B\preceq I$, and let $w_j\ge0$ be weights with $\sum_jw_j=1$ and $\sum_jw_jA_j=B$. Then
--   $$
--   \sum_{j\in J}w_j\int_0^\infty\big(K_{A_j}(s)-K_B(s)\big)^*\big(K_{A_j}(s)-K_B(s)\big)\,ds\ \preceq\ \sum_{j\in J}w_j\,A_j\log A_j-B\log B ,
--   $$
--   where the integrals are integrals of matrix-valued functions over $(0,\infty)$ with respect to Lebesgue measure.
--
--   The left-hand side is positive semidefinite, so the theorem is a quantitative strengthening of the operator Jensen inequality $B\log B\preceq\sum_jw_jA_j\log A_j$ for the operator convex function $t\log t$: the Jensen gap dominates the averaged squared distance between the kernel of each $A_j$ and the kernel of their average $B$. In the surrounding development the kernels are assembled into purifications of effects whose Gram matrices are exactly such kernel integrals, so the theorem bounds the distance between the purification of each $A_j$ and that of $B$ by an entropy gap.
--
--   **Formalization Note** `purificationKernel A s` is `A * (A + s • 1)⁻¹` with Lean's matrix inverse (which is $0$ for singular matrices; $A+sI$ is invertible for $s>0$), and `effectEntropy A` is `cfc (fun t => t * Real.log t) A`. The order is Mathlib's Loewner partial order on matrices, made available by local instances, and the integrals are Bochner integrals over `Ioi 0`. The hypotheses are `PosSemidef` for each $A_j$ and for $B$, the order bounds `A j ≤ 1` and `B ≤ 1`, and the conditions on the weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/SpectralEntropy.lean#L321-L348

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.Resolvent
universe u_n u_α u_m u_p u_r u_J
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped BigOperators MatrixOrder ComplexOrder Topology Matrix.Norms.Elementwise
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

theorem OAI.ThresholdParallelRepetition.Resolvent.weighted_distance_jensen {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (hB : B.PosSemidef) (hB1 : B ≤ 1)
    (hw0 : ∀ j, 0 ≤ w j) (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B) :
    (∑ j, w j • (∫ s : ℝ in Ioi 0,
        (purificationKernel (A j) s - purificationKernel B s)ᴴ *
          (purificationKernel (A j) s - purificationKernel B s))) ≤
      (∑ j, w j • effectEntropy (A j)) - effectEntropy B := by sorry
