-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_ons_sum_R_bound
-- name    : LogRegretOCO.ONS.ons_sum_R_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:02:11.785803+00:00
-- url     : https://prove2.me/theorems/f0aaa815-06ae-4276-bcf8-bdeb161eb6c9
-- title:
--   Proof of Theorem 2 — bound on $\sum_t R_t$
-- statement:
--   Throughout, $\mathcal P \subseteq \mathbb R^n$ is convex and closed, $D > 0$ satisfies $\|y - z\|_2 \le D$ for all $y, z \in \mathcal P$, and $\alpha, G > 0$. The losses $f_1, f_2, \dots : \mathbb R^n \to \mathbb R$ are differentiable at every point of $\mathcal P$, satisfy $\|\nabla f_t(y)\|_2 \le G$ for $y \in \mathcal P$, and are $\alpha$-exp-concave on $\mathcal P$ (so in particular convex on $\mathcal P$). The points $x_1, x_2, \dots$ are a run of Online Newton Step (Fig. 2): $x_1 \in \mathcal P$ is arbitrary and
--   $$
--   x_{t+1} = \Pi_{\mathcal P}^{A_t}\Bigl(x_t - \tfrac{1}{\beta} A_t^{-1} \nabla_t\Bigr), \qquad t \ge 1,
--   $$
--   with $\nabla_t = \nabla f_t(x_t)$, $\beta = \tfrac12 \min\{\tfrac{1}{4GD}, \alpha\}$, $\varepsilon = \tfrac{1}{\beta^2 D^2}$, $A_t = \sum_{i=1}^t \nabla_i \nabla_i^\top + \varepsilon I_n$, and $\Pi_{\mathcal P}^{A}(y) = \operatorname{argmin}_{x \in \mathcal P} (y - x)^\top A (y - x)$.
--
--   Let $R_t(u) = \nabla_t^\top (x_t - u) - \frac{\beta}{2}(u - x_t)^\top \nabla_t \nabla_t^\top (u - x_t)$ (the quantity $R_t$ of (3), p. 177, with the comparator $u$ in place of $x^*$). Then for every $T \ge 1$ and every $u \in \mathcal P$,
--   $$
--   \sum_{t=1}^T R_t(u) \le \frac{1}{2\beta}\sum_{t=1}^T \nabla_t^\top A_t^{-1}\nabla_t + \frac{\beta}{2}(x_1 - u)^\top (A_1 - \nabla_1\nabla_1^\top)(x_1 - u).
--   $$
--   This is the summed per-step inequality after the telescoping $A_t$-distances have absorbed the quadratic terms of the $R_t$.
--
--   Differences from the source:
--   - generalization: the inequality for x* ∈ argmin_{x∈P} Σ_{t=1}^T f_t(x), the best decision in hindsight → the inequality for every u ∈ P; reason: x* ∈ P, so the Lean statement specializes to the paper's at u = x*
--   - encoding: R_t ≜ ∇_tᵀ(x_t − x*) − (β/2)(x* − x_t)ᵀ∇_t∇_tᵀ(x* − x_t), (3) → the expression ⟪∇_t, x_t − u⟫ − β/2 ⟪∇_t, u − x_t⟫² written inline; reason: the same real number
--   - generalization: D is the diameter of P, D = max_{x,y∈P} ‖x − y‖₂ (p. 172) → any real D > 0 with ‖y − z‖ ≤ D for all y, z ∈ P, and ONS uses this D in β and ε; reason: the proof uses D only through ‖x_1 − x*‖ ≤ D and |∇f_t(y)ᵀ(x − y)| ≤ GD; taking D = diam P recovers the paper's statement whenever diam P > 0
--   - encoding: G and D positive implicitly (β = ½ min{1/(4GD), α} and ε = 1/(β²D²) divide by them) → hypotheses 0 < G and 0 < D; reason: the conditions only exclude the cases in which the paper's β and ε are undefined
--   - generalization: the losses are twice differentiable (standing assumption, p. 172) → f_t : ℝⁿ → ℝ differentiable at every point of P, with ∇f_t its gradient; reason: the proof of Theorem 2 (and of Lemma 3) uses only first derivatives; twice differentiable functions satisfy the hypothesis
--   - encoding: the losses are convex (standing assumption, pp. 171–172) → no separate convexity hypothesis; reason: convexity of f_t on P follows from α-exp-concavity with α > 0: −αf_t = log(exp(−αf_t)) is concave as the log of a positive concave function, so the hypothesis would be redundant
--   - generalization: exp(−αf_t(x)) is a concave function of x ∈ P, i.e. ∇²[exp(−αf_t(x))] ⪯ 0 (p. 173) → ConcaveOn ℝ P (fun x => exp(−α f_t x)); reason: the paper's first wording is concavity on P; its Hessian form implies ConcaveOn on the convex set P, but not conversely when P has empty interior
--   - encoding: P non-empty and bounded (standing assumption, p. 171) → no separate hypotheses; reason: non-emptiness follows from x_1 ∈ P (part of IsONSRun) and boundedness from the bound D on distances
--   - encoding: Fig. 2: x_t = Π_P^{A_{t−1}}(x_{t−1} − (1/β)A_{t−1}^{−1}∇_{t−1}) for t > 1, Π an argmin → IsONSRun: x_{t+1} satisfies IsGenProj (minimizer predicate) for A_t at x_t − β⁻¹ A_t⁻¹ ∇_t, for every t ≥ 1; A_t⁻¹ is Matrix.inv; reason: index shift t ↦ t + 1 as in the proof (x_{t+1} = Π^{A_t}(y_{t+1}), p. 177); A_t is positive definite (ε > 0), so Matrix.inv is the inverse; for P non-empty, closed, bounded the minimizer exists and is unique, so the paper's run is exactly a Lean run
--   - encoding: losses f_1, …, f_T for a horizon T → an infinite sequence f : ℕ → (ℝⁿ → ℝ) with the hypotheses for every t ≥ 1 (f_0, x_0 unused); reason: any finite sequence extends by f_t = 0 for t > T (0 satisfies every hypothesis) and the run extends because the generalized projection exists on the compact P; the statement for horizon T involves only f_1, …, f_T and x_1, …, x_{T+1}
--   - reading: ‖∇f(x)‖ ≤ G in the theorem's sentence → ‖∇f_t(y)‖₂ ≤ G for every t ≥ 1 and every y ∈ P; reason: p. 172 defines the gradient bound as sup_{x∈P, t∈[T]} ‖∇f_t(x)‖₂ ≤ G
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, proof of Theorem 2, unnumbered display, p. 178 (PDF p. 10); R_t defined in (3), p. 177 (PDF p. 9)

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_qform
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn
import Definitions.Def_LogRegretOCO_ONS_onsBeta
import Definitions.Def_LogRegretOCO_ONS_onsEps
import Definitions.Def_LogRegretOCO_ONS_onsGrad
import Definitions.Def_LogRegretOCO_ONS_onsA
import Definitions.Def_LogRegretOCO_ONS_IsGenProj
import Definitions.Def_LogRegretOCO_ONS_IsONSRun
open Matrix

namespace LogRegretOCO.ONS

/-- **Summed bound on `Σ R_t` (proof of Theorem 2).**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, proof of Theorem 2, unnumbered display, p. 178:
"Thus, we have Σ_{t=1}^T R_t ≤ (1/2β) Σ_{t=1}^T ∇_tᵀA_t^{−1}∇_t + (β/2)(x_1 − x*)ᵀ(A_1 − ∇_1∇_1ᵀ)(x_1 − x*)",
with `R_t` defined in (3), p. 177: "R_t ≜ ∇_tᵀ(x_t − x*) − (β/2)(x* − x_t)ᵀ∇_t∇_tᵀ(x* − x_t)".

For every `T ≥ 1` and every `u ∈ P`, with `R_t(u) = ⟪∇_t, x_t − u⟫ − (β/2)⟪∇_t, u − x_t⟫²`:
`Σ_{t=1}^T R_t(u) ≤ (1/(2β)) Σ_{t=1}^T ∇_tᵀA_t⁻¹∇_t + (β/2)(x_1 − u)ᵀ(A_1 − ∇_1∇_1ᵀ)(x_1 − u)`.

Common hypotheses (the standing assumptions of §2.1–2.2, pp. 171–173, and of Theorem 2):
`P ⊆ ℝⁿ` convex and closed; `D > 0` bounds the distance between any two points of `P`; `α > 0`,
`G > 0`; every loss `f_t` (`t ≥ 1`) is differentiable at every point of `P`, has
`‖∇f_t(y)‖₂ ≤ G` on `P` and is `α`-exp-concave on `P`; `x` is a run of ONS (Fig. 2) with
parameters `G, D, α`. `P` is non-empty because `x_1 ∈ P` and bounded because of the `D` bound.

**Formalization Note.** Stated for every `u ∈ P` instead of the hindsight minimizer `x*`.
`(x* − x_t)ᵀ∇_t∇_tᵀ(x* − x_t)` is written `⟪∇_t, u − x_t⟫²`. -/
theorem ons_sum_R_bound {n : ℕ} {P : Set (EuclideanSpace ℝ (Fin n))} {G D α : ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hPc : Convex ℝ P) (hPcl : IsClosed P)
    (hD : 0 < D) (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hα : 0 < α) (hG : 0 < G)
    (hdiff : ∀ t : ℕ, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (f t) y)
    (hgrad : ∀ t : ℕ, 1 ≤ t → ∀ y ∈ P, ‖gradient (f t) y‖ ≤ G)
    (hexp : ∀ t : ℕ, 1 ≤ t → IsExpConcaveOn α P (f t))
    (hrun : IsONSRun P G D α f x) :
    ∀ T : ℕ, 1 ≤ T → ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, (inner ℝ (onsGrad f x t) (x t - u) - onsBeta G D α / 2 * inner ℝ (onsGrad f x t) (u - x t) ^ 2) ≤
        1 / (2 * onsBeta G D α) * (∑ t ∈ Finset.Icc 1 T, WithLp.ofLp (onsGrad f x t) ⬝ᵥ ((onsA (onsEps G D α) f x t)⁻¹ *ᵥ WithLp.ofLp (onsGrad f x t)))
          + onsBeta G D α / 2 * qform (onsA (onsEps G D α) f x 1 -
              Matrix.vecMulVec (WithLp.ofLp (onsGrad f x 1)) (WithLp.ofLp (onsGrad f x 1))) (x 1 - u) := by sorry

end LogRegretOCO.ONS
