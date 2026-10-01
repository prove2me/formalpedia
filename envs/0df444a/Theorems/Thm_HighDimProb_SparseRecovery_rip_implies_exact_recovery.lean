-- Prove2me | Theorems.Thm_HighDimProb_SparseRecovery_rip_implies_exact_recovery
-- name    : HighDimProb.SparseRecovery.rip_implies_exact_recovery
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:11:49.248988+00:00
-- url     : https://prove2.me/theorems/f2c302b2-31bc-46d8-9a9c-7f5de826d428
-- title:
--   Theorem 10.5.10 — RIP implies exact recovery
-- statement:
--   This is a purely deterministic, linear-algebraic theorem — no randomness — showing that the
--   restricted isometry property is a sufficient condition for exact recovery of a sparse signal
--   by $\ell_1$ minimization, the deterministic counterpart to the probabilistic Theorem 10.5.1.
--
--   Suppose an $m\times n$ matrix $A$ satisfies RIP with parameters $\alpha,\beta$ and
--   $(1+\lambda)s$, where $\lambda > (\beta/\alpha)^2$. Then every $s$-sparse vector $x\in\mathbb
--   R^n$ is recovered exactly by solving the program
--   $$
--   \text{minimize } \|x'\|_1 \text{ subject to } y = Ax',
--   $$
--   where $y := Ax$: every solution $\hat x$ of this program satisfies $\hat x = x$.
--
--   **Formalization Note** A solution $\hat x$ "of the program" is formalized as an explicit
--   membership in the argmin of the exact feasible set: $\hat x$ is feasible ($A\hat x = Ax$) and
--   optimal ($\|\hat x\|_1 \le \|x'\|_1$ for every feasible $x'$) — not "there exists an estimator
--   such that", which would prove a different, weaker statement (the trivialization risk this
--   chapter's triage brief flags explicitly). The conclusion holds for every such $\hat x$, not
--   just one witness.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 260, Theorem 10.5.10

import Mathlib
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
import Definitions.Def_HighDimProb_SparseRecovery_L1Norm
import Definitions.Def_HighDimProb_SparseRecovery_Sparsity
import Definitions.Def_HighDimProb_SparseRecovery_RIP

namespace HighDimProb.SparseRecovery

/-- **Theorem 10.5.10** (RIP implies exact recovery), Vershynin, *High-Dimensional Probability*
(2018), p. 260 (PDF p. 268).

"Suppose an `m × n` matrix `A` satisfies RIP with some parameters `α, β` and `(1+λ)s`, where
`λ > (β/α)²`. Then every `s`-sparse vector `x ∈ ℝⁿ` can be recovered exactly by solving the
program (10.12), i.e. the solution satisfies `x̂ = x`." Program (10.12), p. 258 (PDF p. 266):
"minimize `‖x'‖₁` subject to `y = Ax'`", with `y := Ax` the (noiseless) measurement.

A solution `x̂` "of the program (10.12)" is formalized as: `x̂` is feasible (`A.mulVec x̂ =
A.mulVec x`, i.e. `y = Ax̂`) and optimal (`‖x̂‖₁ ≤ ‖x'‖₁` for every feasible `x'`) — an explicit
membership in the argmin of the exact feasible set, per `BRIEF.md`'s own flagged pitfall against
"there exists an estimator such that", which would prove a different, weaker statement. The
conclusion is stated for *every* such `x̂` (not just one witness), which both matches "the
solution satisfies `x̂ = x`" and, since RIP forces uniqueness, is not a stronger claim than the
book's own. `0 < α` is needed for `(β/α)²` to be the ratio the book intends; the book's own
hypothesis `λ > (β/α)²` is kept verbatim, so no case of the book's own theorem is excluded. -/
theorem rip_implies_exact_recovery {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (α β s lam : ℝ)
    (hα : 0 < α) (hlam : lam > (β / α) ^ 2)
    (hRIP : SatisfiesRIP A α β ((1 + lam) * s)) (x : Fin n → ℝ) (hx : IsSSparse x s)
    (xhat : Fin n → ℝ) (hfeas : A.mulVec xhat = A.mulVec x)
    (hopt : ∀ x' : Fin n → ℝ, A.mulVec x' = A.mulVec x → l1Norm xhat ≤ l1Norm x') :
    xhat = x := by sorry

end HighDimProb.SparseRecovery
