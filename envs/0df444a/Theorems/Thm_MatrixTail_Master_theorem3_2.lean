-- Prove2me | Theorems.Thm_MatrixTail_Master_theorem3_2
-- name    : MatrixTail.Master.theorem3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:15:17.668608+00:00
-- url     : https://prove2.me/theorems/190e269e-f0f0-4901-b647-20f381697ffd
-- title:
--   Theorem 3.2 (Lieb) — A ↦ tr exp(H + log A) is concave on the positive-definite cone
-- statement:
--   Fix a $d\times d$ complex Hermitian matrix $H$. The function
--   $$A \longmapsto \operatorname{tr}\exp\bigl(H + \log A\bigr)$$
--   is concave on the cone of $d\times d$ positive-definite matrices: for positive-definite $A, B$ and $\tau\in[0,1]$,
--   $$\tau\operatorname{tr}\exp(H+\log A) + (1-\tau)\operatorname{tr}\exp(H+\log B) \le \operatorname{tr}\exp\bigl(H+\log(\tau A+(1-\tau)B)\bigr).$$
--
--   This is Lieb's concavity theorem (Lieb 1973, Thm. 6), which the paper cites without proof; Epstein (1973) and Tropp (2011, via joint convexity of quantum relative entropy) give alternative proofs. It is the engine behind the subadditivity of matrix cumulant generating functions.
--
--   **Formalization Note.** $\log A$ is defined by the spectral calculus on positive-definite $A$; concavity is taken on the positive-definite cone, not the positive-semidefinite one, where $\log$ is undefined.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 10, Theorem 3.2 (citing Lieb 1973, Thm. 6)

import Mathlib
import Definitions.Def_MatrixTail_Master_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Master

/-- **Theorem 3.2 (Lieb).** Tropp, *User-Friendly Tail Bounds for Sums of Random Matrices*, arXiv:1004.4389v7,
p. 10: "Fix a self-adjoint matrix `H`. The function `A ↦ tr exp(H + log(A))` is concave on the
positive-definite cone."

The paper cites this result from Lieb [Lie73, Thm. 6] without proof; Epstein [Eps73, Sec. II] and Tropp
[Tro11b] (via the joint convexity of quantum relative entropy) give alternative proofs.

**Formalization Note.** Matrices are complex `d × d`. The positive-definite cone is
`{A | A.PosDef}` (not the positive-semidefinite cone, on which `log` is not defined); `log A` is
`cfc Real.log A` and `tr exp(·)` is `trExp`, the real part of the trace of `cfc Real.exp (·)`. Concavity is
Mathlib's `ConcaveOn ℝ`, which includes the convexity of the cone. -/
theorem theorem3_2 {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef} (fun A => trExp (H + mlog A)) := by sorry

end MatrixTail.Master
