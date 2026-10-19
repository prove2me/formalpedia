-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_OperatorEntropy_effectEntropy_nonpos
-- name    : OAI.ThresholdParallelRepetition.OperatorEntropy.effectEntropy_nonpos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:00:18.868997+00:00
-- url     : https://prove2.me/theorems/5ea2f90b-be74-4680-9e04-01c80d165ccb
-- title:
--   The operator $A\log A$ is negative semidefinite for every effect $0\le A\le I$
-- statement:
--   Let $n$ be a finite index set and let $A\in\mathbb{C}^{n\times n}$ be positive semidefinite with $A\le I$ in the Loewner order (an effect). Define $A\log A$ by functional calculus: if $A=\sum_i\lambda_iu_iu_i^*$ is a spectral decomposition, then $A\log A=\sum_i\lambda_i\log\lambda_i\,u_iu_i^*$, with the convention $0\log0=0$. Then
--
--   $$
--   A\log A\;\le\;0 ,
--   $$
--
--   that is, $-A\log A$ is positive semidefinite.
--
--   This is the operator form of the scalar fact $t\log t\le0$ for $t\in[0,1]$: the operator entropy $-A\log A$ of an effect is positive semidefinite. It fixes the sign of the entropic potentials built from effects.
--
--   **Formalization Note** $A\log A$ is `effectEntropy A := cfc (fun t : ℝ => t * Real.log t) A`, the continuous functional calculus for Hermitian matrices; Lean's $\log0=0$ gives $0\log0=0$. The order $\le$ on matrices is the Loewner order (`MatrixOrder`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/RelativeEntropy.lean#L124-L136

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
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.OperatorEntropy
universe u_ι u_α u_β u_n u_m
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open Resolvent QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

theorem OAI.ThresholdParallelRepetition.OperatorEntropy.effectEntropy_nonpos {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA1 : A ≤ 1) :
    effectEntropy A ≤ 0 := by sorry
