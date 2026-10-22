-- Prove2me | Theorems.Thm_GradDOvS_Submod_eq_6
-- name    : GradDOvS.Submod.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:50.834965+00:00
-- url     : https://prove2.me/theorems/52d57539-7b5b-425e-af20-85adfb2b557c
-- title:
--   Eq. (6), p. 18 — the Lovász extension is a convex combination of f at the neighbouring points
-- statement:
--   Let $f : \{0,1\}^d \to \mathbb R$, $\bar x \in [0,1]^d$ and $\alpha$ a consistent permutation of $\bar x$, with neighbouring points $S^0,\dots,S^d$. Then
--   $$\tilde f(\bar x) = \big[1 - \bar x_{\alpha(1)}\big] f(S^0) + \sum_{i=1}^{d-1} \big[\bar x_{\alpha(i)} - \bar x_{\alpha(i+1)}\big] f(S^i) + \bar x_{\alpha(d)} f(S^d), \tag{6}$$
--   the weights are nonnegative and sum to $1$, and consequently some neighbouring point satisfies
--   $$f(S^i) \le \tilde f(\bar x).$$
--
--   This is what makes rounding possible: an $\epsilon$-optimal point of the relaxed problem has an $\epsilon$-optimal neighbouring point.
--
--   **Formalization Note** Indices are 0-based. With $x_s(i) = \bar x_{\alpha(i+1)}$ for $i < d$ and $x_s(d) = 0$, the weight of $f(S^i)$ is $w_i = x_s(i-1) - x_s(i)$, with $x_s(-1) := 1$; this is (6) for $d \ge 1$ and also covers $d = 0$. The formula (2) is evaluated with the same permutation $\alpha$. No submodularity is needed.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 18, eq. (6) and the sentence after it

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Eq. (6), p. 18: for `x ∈ [0,1]^d` and a consistent permutation `α` of `x`, the Lovász
extension is the convex combination
`[1 - x_{α(1)}] f(S^0) + ∑_{i=1}^{d-1} [x_{α(i)} - x_{α(i+1)}] f(S^i) + x_{α(d)} f(S^d)`,
hence some neighbouring point has `f(S^i) ≤ f̃(x)`. Here `xs i = x_{α(i+1)}` (0-based, `xs d = 0`)
and `w i` is the weight of `f(S^i)`. -/
theorem eq_6 {d : ℕ} (f : Finset (Fin d) → ℝ) (x : Fin d → ℝ) (hx : x ∈ box d)
    (α : Equiv.Perm (Fin d)) (hα : IsConsistentPerm x α) :
    let xs : ℕ → ℝ := fun i => if h : i < d then x (α ⟨i, h⟩) else 0
    let w : ℕ → ℝ := fun i => (if i = 0 then 1 else xs (i - 1)) - xs i
    (lovaszWith f x α = ∑ i ∈ Finset.range (d + 1), w i * f (nbr α i)) ∧
      (∀ i ∈ Finset.range (d + 1), 0 ≤ w i) ∧
      (∑ i ∈ Finset.range (d + 1), w i = 1) ∧
      (∃ i ≤ d, f (nbr α i) ≤ lovaszWith f x α) := by sorry

end GradDOvS.Submod
