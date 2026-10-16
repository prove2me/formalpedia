-- Prove2me | Theorems.Thm_OAI_GAD_entropy_diagonal
-- name    : OAI.GAD.entropy_diagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:24:34.670977+00:00
-- url     : https://prove2.me/theorems/165fc90d-27af-45a8-bb63-f0d76a0ae314
-- title:
--   Entropy of a real diagonal matrix
-- statement:
--   Let $\iota$ be a finite index set, let $p:\iota\to\mathbb{R}$ be any real vector, and let $\operatorname{diag}(p)\in\mathbb{C}^{\iota\times\iota}$ be the diagonal matrix with entries $p_i$. Define the matrix entropy $S(A)=\operatorname{Re}\operatorname{Tr}\eta(A)$ through the continuous functional calculus, where $\eta(x)=-x\log x$ (natural logarithm, $\eta(0)=0$). Then
--
--   $$
--   S\bigl(\operatorname{diag}(p)\bigr)=\sum_{i\in\iota}\eta(p_i).
--   $$
--
--   For a probability vector $p$ the right-hand side is the Shannon entropy of $p$ in nats, so the von Neumann entropy of a classical (diagonal) state is the Shannon entropy of its diagonal. This is used whenever states or channel outputs are diagonal in a fixed basis.
--
--   **Formalization Note** No sign condition on $p$ is assumed. For negative entries the formula uses Lean's conventions `Real.negMulLog x = -x * Real.log x` with $\log x=\log|x|$. `entropy` is the real part of the trace of `cfc Real.negMulLog`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/TensorEntropy.lean#L31-L53

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open scoped BigOperators
open Set Filter Topology
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open Matrix
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem OAI.GAD.entropy_diagonal (p : ι → ℝ) :
    entropy (Matrix.diagonal (fun i ↦ (p i : ℂ))) = ∑ i, Real.negMulLog (p i) := by sorry
