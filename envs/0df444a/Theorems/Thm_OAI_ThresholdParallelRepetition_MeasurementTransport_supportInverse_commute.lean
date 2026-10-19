-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MeasurementTransport_supportInverse_commute
-- name    : OAI.ThresholdParallelRepetition.MeasurementTransport.supportInverse_commute
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:43:07.407832+00:00
-- url     : https://prove2.me/theorems/332da92a-1fb4-4ad4-9a7a-29b4f6e4a7a7
-- title:
--   A Hermitian matrix commutes with its support inverse
-- statement:
--   Let $n$ be a finite index set and let $T$ be a Hermitian $n\times n$ complex matrix with spectral decomposition $T=\sum_i\lambda_iu_iu_i^*$. Let
--   $$
--   T^{+}=\sum_{i:\ \lambda_i\neq0}\lambda_i^{-1}\,u_iu_i^*
--   $$
--   be its support inverse, the functional calculus of $t\mapsto t^{-1}$ with the convention $0^{-1}=0$ (the Moore–Penrose pseudoinverse). Then
--   $$
--   T^{+}\,T=T\,T^{+}.
--   $$
--
--   Both products equal $\sum_{i:\lambda_i\neq0}u_iu_i^*$, the orthogonal projection onto the range of $T$. The commutation is used to rearrange products of $T$ and $T^{+}$, for example when computing the Gram matrix of the polar factor $M\,|M|^{+}$ of a matrix $M$.
--
--   **Formalization Note** `supportInverse T` is `cfc (fun t : ℝ => t⁻¹) T`; the hypothesis `T.IsHermitian` makes the functional calculus agree with the spectral description above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/MeasurementTransport.lean#L55-L69

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MeasurementTransport
universe u_n u_m u_A
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
variable {n : Type u_n} [Fintype n] [DecidableEq n]

theorem OAI.ThresholdParallelRepetition.MeasurementTransport.supportInverse_commute {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    supportInverse T * T = T * supportInverse T := by sorry
