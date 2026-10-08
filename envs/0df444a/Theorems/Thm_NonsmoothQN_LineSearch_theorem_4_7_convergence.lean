-- Prove2me | Theorems.Thm_NonsmoothQN_LineSearch_theorem_4_7_convergence
-- name    : NonsmoothQN.LineSearch.theorem_4_7_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:08.818977+00:00
-- url     : https://prove2.me/theorems/5ec5fae8-b4de-40bb-8700-029fa54f864e
-- title:
--   Theorem 4.7, p. 147 — the bisection Armijo–Wolfe line search: final step is Armijo–Wolfe, (4.8) ⇒ termination, else (4.9)
-- statement:
--   Let $h$ satisfy Assumption 4.1 with slope $s=\limsup_{t\downarrow0}h(t)/t<0$, let $0<c_1<c_2<1$, and run Algorithm 4.6, writing $[\alpha_n,\beta_n]$ for the bracket and $t_n$ for the trial step before trial $n=0,1,2,\dots$. Then:
--
--   1. **Correctness.** Whenever a trial step $t_n$ passes both the Armijo test $h(t_n)<c_1st_n$ and the Wolfe test ($h$ differentiable at $t_n$ with $h'(t_n)>c_2s$), it is an Armijo–Wolfe step; in particular $t_n>0$.
--   2. **Termination.** If for every $\bar t>0$ the limit $\lim_{t\uparrow\bar t}h'(t)$ exists in $[-\infty,+\infty]$ (condition (4.8)), the line search terminates.
--   3. **Non-termination.** If the line search does not terminate, then from some $N$ on the brackets $[\alpha_n,\beta_n]$ are finite with $\alpha_n>0$, nested, halving in length at each trial, and each contains a set of nonzero Lebesgue measure of Armijo–Wolfe steps. Moreover $\alpha_n$ and $\beta_n$ converge to a common step $\tilde t>0$ with
--   $$h(\tilde t)=c_1s\tilde t \qquad\text{and}\qquad \limsup_{t\uparrow\tilde t}h'(t)\ \ge\ c_2s. \tag{4.9}$$
--
--   Theorem 4.7 is the convergence theorem for the line search used inside BFGS for nonsmooth problems: a nondifferentiable trial point counts as a Wolfe failure, so the search can only fail on functions whose derivative oscillates near a point, and condition (4.8) excludes this (it holds, for example, for every semi-algebraic $h$).
--
--   **Formalization Note.** Condition (4.8) is read as: $h$ is differentiable on an interval $(t',\bar t)$ and $h'$ has a limit in the extended reals as $t\uparrow\bar t$; this is what the paper's proof (p. 148) uses, and without the differentiability requirement Mathlib's convention $h'(t)=0$ at nondifferentiable points would change its meaning. In (4.9), the $\limsup$ is taken over the points $t<\tilde t$ at which $h$ is differentiable, computed in the extended reals; it is $-\infty$ if there are no such points near $\tilde t$, so the bound is not vacuous. The upper bounds $\beta_n$ are given as the real numbers $b_n$ with $\beta_n=b_n$ for $n\ge N$.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 147, Theorem 4.7, (4.8), (4.9)

import Mathlib
import Definitions.Def_NonsmoothQN_LineSearch_Basic

open Filter Topology MeasureTheory Set

namespace NonsmoothQN.LineSearch

/-- Theorem 4.7 (convergence, p. 147). Under Assumption 4.1 with `0 < c₁ < c₂ < 1`:
(i) whenever Algorithm 4.6 terminates, the final trial step is an Armijo–Wolfe step;
(ii) it terminates under (4.8);
(iii) if it does not terminate, it eventually generates nested finite intervals `[α, β]` halving
in length at each iteration, each containing a set of nonzero measure of Armijo–Wolfe steps, and
these converge to a step `t̃ > 0` with `h(t̃) = c₁ s t̃` and `limsup_{t ↑ t̃} h'(t) ≥ c₂ s` (4.9),
the `limsup` taken over the points `t < t̃` where `h` is differentiable. -/
theorem theorem_4_7_convergence (h : ℝ → ℝ) (c₁ c₂ s : ℝ)
    (hA41 : Assumption41 h s) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    (∀ n : ℕ, ArmijoA h c₁ s (lsRun h c₁ c₂ s n).t → WolfeW h c₂ s (lsRun h c₁ c₂ s n).t →
        IsAWStep h c₁ c₂ s (lsRun h c₁ c₂ s n).t) ∧
    (Cond48 h → Terminates h c₁ c₂ s) ∧
    (¬ Terminates h c₁ c₂ s →
      ∃ N : ℕ, ∃ b : ℕ → ℝ,
        (∀ n ≥ N,
          (lsRun h c₁ c₂ s n).β = (b n : WithTop ℝ) ∧
          0 < (lsRun h c₁ c₂ s n).α ∧
          Set.Icc (lsRun h c₁ c₂ s (n + 1)).α (b (n + 1)) ⊆
            Set.Icc (lsRun h c₁ c₂ s n).α (b n) ∧
          b (n + 1) - (lsRun h c₁ c₂ s (n + 1)).α = (b n - (lsRun h c₁ c₂ s n).α) / 2 ∧
          volume {t | t ∈ Set.Icc (lsRun h c₁ c₂ s n).α (b n) ∧ IsAWStep h c₁ c₂ s t} ≠ 0) ∧
        ∃ tt : ℝ, 0 < tt ∧
          Tendsto (fun n => (lsRun h c₁ c₂ s n).α) atTop (𝓝 tt) ∧
          Tendsto b atTop (𝓝 tt) ∧
          h tt = c₁ * s * tt ∧
          ((c₂ * s : ℝ) : EReal) ≤
            Filter.limsup (fun t => ((deriv h t : ℝ) : EReal))
              (𝓝[Set.Iio tt ∩ {t | DifferentiableAt ℝ h t}] tt)) := by sorry

end NonsmoothQN.LineSearch
