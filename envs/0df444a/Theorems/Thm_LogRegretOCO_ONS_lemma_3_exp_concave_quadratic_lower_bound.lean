-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_lemma_3_exp_concave_quadratic_lower_bound
-- name    : LogRegretOCO.ONS.lemma_3_exp_concave_quadratic_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:00:33.835721+00:00
-- url     : https://prove2.me/theorems/56b29aef-1065-4963-9801-1cce90027326
-- title:
--   Lemma 3 — quadratic lower bound for exp-concave functions
-- statement:
--   Let $\mathcal P \subseteq \mathbb R^n$, let $D > 0$ with $\|y - z\|_2 \le D$ for all $y, z \in \mathcal P$, and let $G, \alpha > 0$. Let $f : \mathbb R^n \to \mathbb R$ be differentiable at every point of $\mathcal P$ with $\|\nabla f(y)\|_2 \le G$ for $y \in \mathcal P$, and such that $\exp(-\alpha f)$ is concave on $\mathcal P$. Then for every real $\beta \le \tfrac12 \min\{\tfrac{1}{4GD}, \alpha\}$,
--   $$
--   f(x) \ge f(y) + \nabla f(y)^\top (x - y) + \frac{\beta}{2}\,(x - y)^\top \nabla f(y) \nabla f(y)^\top (x - y) \qquad \text{for all } x, y \in \mathcal P .
--   $$
--   Exp-concavity thus gives a lower bound on $f$ by its first-order expansion plus a rank-one quadratic term built from the gradient alone, without the Hessian. This is the inequality that turns the regret of Online Newton Step into the quantities $R_t$ of the proof of Theorem 2.
--
--   **Formalization Note** $(x - y)^\top \nabla f(y) \nabla f(y)^\top (x - y)$ is written $\langle \nabla f(y), x - y\rangle^2$; exp-concavity is `IsExpConcaveOn α P f`.
--
--   Differences from the source:
--   - generalization: D is the diameter of P, D = max_{x,y∈P} ‖x − y‖₂ (p. 172) → any real D > 0 with ‖y − z‖ ≤ D for all y, z ∈ P, and ONS uses this D in β and ε; reason: the proof uses D only through ‖x_1 − x*‖ ≤ D and |∇f_t(y)ᵀ(x − y)| ≤ GD; taking D = diam P recovers the paper's statement whenever diam P > 0
--   - encoding: G, D positive implicitly (1/(4GD)); α > 0 standing (p. 173) → hypotheses 0 < G, 0 < D, 0 < α; reason: the conditions only exclude the cases in which β is undefined; α > 0 is the paper's own standing assumption
--   - generalization: the losses are twice differentiable (standing assumption, p. 172) → f_t : ℝⁿ → ℝ differentiable at every point of P, with ∇f_t its gradient; reason: the proof of Theorem 2 (and of Lemma 3) uses only first derivatives; twice differentiable functions satisfy the hypothesis
--   - generalization: exp(−αf_t(x)) is a concave function of x ∈ P, i.e. ∇²[exp(−αf_t(x))] ⪯ 0 (p. 173) → ConcaveOn ℝ P (fun x => exp(−α f_t x)); reason: the paper's first wording is concavity on P; its Hessian form implies ConcaveOn on the convex set P, but not conversely when P has empty interior
--   - encoding: f : P → R → f : ℝⁿ → ℝ, differentiable at every point of P; reason: ∇f(x) needs f around x; only the values on P enter the conclusion
--   - encoding: P convex (standing assumption) → no separate hypothesis; reason: convexity of P is part of ConcaveOn ℝ P
--   - generalization: P closed and non-empty (standing assumption, p. 171) → not assumed; reason: the lemma does not use them; the paper's setting is a special case
--   - encoding: (x − y)ᵀ∇f(y)∇f(y)ᵀ(x − y) → ⟪∇f(y), x − y⟫²; reason: the same real number
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, Lemma 3, p. 177 (PDF p. 9)

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn

namespace LogRegretOCO.ONS

/-- **Lemma 3 (exp-concave functions admit a quadratic lower bound).**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, Lemma 3, p. 177:
"For a function f : P → R, where P has diameter D, such that ∀x ∈ P, ‖∇f(x)‖ ≤ G and
exp(−αf(x)) is concave, the following holds for β ≤ 1/2 min{1/(4GD), α}:
∀x, y ∈ P: f(x) ≥ f(y) + ∇f(y)ᵀ(x − y) + (β/2)(x − y)ᵀ∇f(y)∇f(y)ᵀ(x − y)."

**Formalization Note.** `f` is a real function on `ℝⁿ = EuclideanSpace ℝ (Fin n)`,
differentiable at every point of `P`, with Mathlib's `gradient`. "P has diameter D" is encoded
as `D > 0` with `‖y − z‖ ≤ D` on `P` (any bound on the diameter). Exp-concavity is
`ConcaveOn ℝ P (exp(−α f))` (which makes `P` convex), with the standing `α > 0` of p. 173.
`(x − y)ᵀ∇f(y)∇f(y)ᵀ(x − y)` is written `⟪∇f(y), x − y⟫²`. `β` is any real number with the
stated bound, as printed. -/
theorem lemma_3_exp_concave_quadratic_lower_bound {n : ℕ} {P : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ} {G D α β : ℝ}
    (hD : 0 < D) (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hG : 0 < G) (hα : 0 < α)
    (hdiff : ∀ y ∈ P, DifferentiableAt ℝ f y)
    (hgrad : ∀ y ∈ P, ‖gradient f y‖ ≤ G)
    (hexp : IsExpConcaveOn α P f)
    (hβ : β ≤ 1 / 2 * min (1 / (4 * G * D)) α) :
    ∀ x ∈ P, ∀ y ∈ P,
      f y + inner ℝ (gradient f y) (x - y) + β / 2 * inner ℝ (gradient f y) (x - y) ^ 2 ≤ f x := by sorry

end LogRegretOCO.ONS
