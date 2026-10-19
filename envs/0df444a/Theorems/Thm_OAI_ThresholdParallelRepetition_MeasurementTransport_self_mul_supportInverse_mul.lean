-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MeasurementTransport_self_mul_supportInverse_mul
-- name    : OAI.ThresholdParallelRepetition.MeasurementTransport.self_mul_supportInverse_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:41:22.855456+00:00
-- url     : https://prove2.me/theorems/b82950d2-8eef-4fa9-8588-c1e1e1affe10
-- title:
--   A Hermitian matrix satisfies $TT^{+}T=T$ for its support inverse
-- statement:
--   Let $n$ be a finite index set and let $T$ be a Hermitian $n\times n$ complex matrix with spectral decomposition $T=\sum_i\lambda_iu_iu_i^*$ ($\lambda_i\in\mathbb R$, $(u_i)$ an orthonormal eigenbasis). Its support inverse is obtained by applying $t\mapsto t^{-1}$ to the eigenvalues, with the convention $0^{-1}=0$:
--   $$
--   T^{+}=\sum_{i:\ \lambda_i\neq0}\lambda_i^{-1}\,u_iu_i^* ,
--   $$
--   which is the Moore–Penrose pseudoinverse of $T$. Then
--   $$
--   T\,T^{+}\,T=T .
--   $$
--
--   This is the defining identity of a generalized inverse. It is used to show that $TT^{+}$ and $T^{+}T$ act as the identity on the range of $T$, for instance when measurement operators are transported through a matrix $F$ with $T=F^*F$, and when a matrix is recovered from its polar factor and its absolute value.
--
--   **Formalization Note** `supportInverse T` is `cfc (fun t : ℝ => t⁻¹) T`, the continuous functional calculus of the real function $t\mapsto t^{-1}$; Lean's convention that the inverse of $0$ is $0$ is what makes it the pseudoinverse. The hypothesis `T.IsHermitian` is needed: for a non-Hermitian matrix the real functional calculus is $0$ by convention.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/MeasurementTransport.lean#L40-L53

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

theorem OAI.ThresholdParallelRepetition.MeasurementTransport.self_mul_supportInverse_mul {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    T * supportInverse T * T = T := by sorry
