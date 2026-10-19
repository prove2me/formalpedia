-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_OperatorEntropy_functional_entropy_lower
-- name    : OAI.ThresholdParallelRepetition.OperatorEntropy.functional_entropy_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:01:48.096107+00:00
-- url     : https://prove2.me/theorems/8a6aeab8-7aad-44a6-a897-bafdf6dfb8d5
-- title:
--   Entropy lower bound for positive subunital functionals: $-\Phi(A\log A)\le\eta(\Phi(A))$
-- statement:
--   Let $n$ be a finite index set and let $\Phi:\mathbb{C}^{n\times n}\to\mathbb{R}$ be a real-linear map such that $\Phi(S)\ge0$ for every positive semidefinite $S$ and $\Phi(I)\le1$. Let $\eta(t)=-t\log t$ (with $\eta(0)=0$) and, for a positive semidefinite $A=\sum_i\lambda_iu_iu_i^*$, let $A\log A=\sum_i\lambda_i\log\lambda_i\,u_iu_i^*$ be defined by functional calculus. Then for every positive semidefinite $A\in\mathbb{C}^{n\times n}$,
--
--   $$
--   -\Phi(A\log A)\;\le\;\eta\bigl(\Phi(A)\bigr)=-\Phi(A)\log\Phi(A).
--   $$
--
--   This is a noncommutative Jensen inequality: evaluating the operator entropy under a positive subunital functional yields at most the scalar entropy of the evaluated operator. For instance, with $\Phi(S)=\operatorname{Re}\operatorname{tr}(\rho S)$ for a positive semidefinite $\rho$ with $\operatorname{tr}\rho\le1$ it bounds $-\operatorname{tr}(\rho\,A\log A)$ by $\eta(\operatorname{tr}(\rho A))$; in this development it is applied to quadratic forms $S\mapsto\operatorname{Re}\langle v,(S\otimes B)v\rangle$ of a bipartite vector with a fixed effect $B$ on the other factor.
--
--   **Formalization Note** $\Phi$ has type `Matrix n n ℂ →ₗ[ℝ] ℝ`, so it is defined and real-linear on all complex matrices, while positivity is assumed only on positive semidefinite ones. $A\log A$ is `effectEntropy A := cfc (fun t : ℝ => t * Real.log t) A`, and $\eta$ is `Real.negMulLog`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/RelativeEntropy.lean#L159-L185

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

theorem OAI.ThresholdParallelRepetition.OperatorEntropy.functional_entropy_lower (Φ : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (hΦ : ∀ A : Matrix n n ℂ, A.PosSemidef → 0 ≤ Φ A)
    (hmass : Φ 1 ≤ 1) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    -Φ (effectEntropy A) ≤ Real.negMulLog (Φ A) := by sorry
