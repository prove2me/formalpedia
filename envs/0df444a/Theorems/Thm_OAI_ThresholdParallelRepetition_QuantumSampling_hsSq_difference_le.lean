-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_hsSq_difference_le
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_difference_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:56:23.252046+00:00
-- url     : https://prove2.me/theorems/daa5fe82-cfde-49f7-96de-dfe5421939df
-- title:
--   Difference of squared Hilbert–Schmidt norms in the unit ball is at most twice the distance
-- statement:
--   Let $m$ and $n$ be finite index sets and let $M,N\in\mathbb{C}^{m\times n}$ be complex matrices. Write $\|M\|_2=\bigl(\sum_{i,j}|M_{ij}|^2\bigr)^{1/2}$ for the Hilbert–Schmidt (Frobenius) norm. If $\|M\|_2^2\le1$ and $\|N\|_2^2\le1$, then
--
--   $$
--   \|M\|_2^2-\|N\|_2^2\;\le\;2\,\|M-N\|_2 .
--   $$
--
--   Viewing $M$ and $N$ as subnormalized vectors, the inequality says that squared norms, and hence probabilities of the form $\|\sqrt{W}\,v\|^2$ for an effect $0\le W\le I$, change at most linearly in the distance between the vectors. It is used to compare winning probabilities of nearby subnormalized bipartite states.
--
--   **Formalization Note** $\|M\|_2^2$ is `hsSq M`, the sum of `Complex.normSq` of the entries, and the right-hand side is written `2 * Real.sqrt (hsSq (M - N))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/CorrelatedSampling.lean#L29-L42

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
universe u_m u_n u_A u_B u_p u_ι
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]

theorem OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_difference_le (M N : Matrix m n ℂ) (hM : hsSq M ≤ 1) (hN : hsSq N ≤ 1) :
    hsSq M - hsSq N ≤ 2 * Real.sqrt (hsSq (M-N)) := by sorry
