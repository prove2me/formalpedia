-- Prove2me | Theorems.Thm_OAI_GAD_hasDerivAt_matrix_mul
-- name    : OAI.GAD.hasDerivAt_matrix_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:06:58.052739+00:00
-- url     : https://prove2.me/theorems/14021901-6704-4664-a9e9-9e505454afb7
-- title:
--   Product rule for differentiable curves of complex matrices
-- statement:
--   Let $\iota$ be a finite index set and let $A,B:\mathbb{R}\to\mathbb{C}^{\iota\times\iota}$ be curves of square complex matrices that are differentiable at $t\in\mathbb{R}$, with derivatives $A'(t)=H$ and $B'(t)=K$. Then the pointwise product $s\mapsto A(s)B(s)$ is differentiable at $t$, and
--
--   $$
--   \frac{d}{ds}\Big|_{s=t}A(s)B(s)=H\,B(t)+A(t)\,K .
--   $$
--
--   The order of the factors matters because matrix multiplication is not commutative. This product rule is used to differentiate the matrix inverse and expressions such as $\operatorname{tr}\bigl(A(s)^{-1}H\bigr)$ along curves of matrices.
--
--   **Formalization Note** The derivatives are `HasDerivAt` statements for functions `ℝ → Matrix ι ι ℂ`, with matrices carrying the entrywise topology; in finite dimension this agrees with differentiability for any norm. No decidable equality on $\iota$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean#L46-L62

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators
open Matrix
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem OAI.GAD.hasDerivAt_matrix_mul {A B : ℝ → Matrix ι ι ℂ}
    {H K : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hB : HasDerivAt B K t) :
    HasDerivAt (fun s ↦ A s * B s) (H * B t + A t * K) t := by sorry
