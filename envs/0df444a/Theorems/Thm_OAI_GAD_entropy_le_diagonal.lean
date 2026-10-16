-- Prove2me | Theorems.Thm_OAI_GAD_entropy_le_diagonal
-- name    : OAI.GAD.entropy_le_diagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:14:35.629187+00:00
-- url     : https://prove2.me/theorems/048fafa4-e1d0-429e-99c5-8a5feb2c336b
-- title:
--   Entropy of a positive semidefinite matrix is at most the entropy of its diagonal
-- statement:
--   Let $\iota$ be a finite index set and let $A\in\mathbb{C}^{\iota\times\iota}$ be a positive semidefinite matrix with eigenvalues $\lambda_j\ge 0$ ($j\in\iota$, counted with multiplicity). Write $\eta(x)=-x\log x$ (natural logarithm, $\eta(0)=0$) and let $S(A)=\operatorname{Tr}\eta(A)=\sum_{j\in\iota}\eta(\lambda_j)$ be the von Neumann entropy of $A$, defined through the functional calculus and without any normalization of the trace. The diagonal entries $A_{ii}$ are real and nonnegative, and
--
--   $$
--   S(A)\le\sum_{i\in\iota}\eta(A_{ii}).
--   $$
--
--   In words: replacing a positive semidefinite matrix by its diagonal in a fixed orthonormal basis (complete dephasing, or pinching) can only increase the entropy. This is the basic comparison between the quantum entropy of a matrix and the classical entropy of its diagonal, and it is the key step in proving concavity of $S$ on the positive semidefinite cone.
--
--   **Formalization Note** `entropy A` is the real part of the trace of `cfc Real.negMulLog A`; for a positive semidefinite matrix it equals $\sum_j\eta(\lambda_j)$. The right-hand side uses the real parts `(A i i).re` of the diagonal entries.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/SpectralEntropy.lean#L74-L91

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity

open OAI OAI.GAD
universe u_1
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.entropy_le_diagonal {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    entropy A ≤ ∑ i, Real.negMulLog (A i i).re := by sorry
