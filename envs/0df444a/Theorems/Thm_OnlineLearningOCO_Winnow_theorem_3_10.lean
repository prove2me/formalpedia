-- Prove2me | Theorems.Thm_OnlineLearningOCO_Winnow_theorem_3_10
-- name    : OnlineLearningOCO.Winnow.theorem_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:53.520569+00:00
-- url     : https://prove2.me/theorems/814dfbcf-c719-486a-9ac1-f2ea51258566
-- title:
--   Theorem 3.10 — Winnow makes at most $(\sum_t f_t(u)+k\log(d)/\eta)/(1-2\eta)$ mistakes, and $8k\log d$ on separable $k$-disjunctions
-- statement:
--   Let $d,k$ be positive integers with $k\ge1$ and $0<\eta<1/2$. Run Winnow with parameter $\eta$ on $(x_1,y_1),\dots,(x_T,y_T)$ with $x_t\in\{0,1\}^d$ and $y_t\in\{-1,1\}$; let $\mathcal M\subseteq\{1,\dots,T\}$ be the rounds on which it errs and $f_t(w)=\mathbf 1_{[t\in\mathcal M]}[1-y_t(2\langle w,x_t\rangle-1)]_+$. Then for every $u\in\{0,1\}^d$ with $\|u\|_1=k$,
--   $$|\mathcal M|\le\sum_{t=1}^T f_t(w_t)\le\frac{1}{1-2\eta}\Bigl(\sum_{t=1}^T f_t(u)+\frac{k\log d}{\eta}\Bigr).$$
--   In particular, if $y_t(2\langle u,x_t\rangle-1)\ge1$ for all $t$ (the sequence is labelled by the $k$-literal monotone disjunction with relevant variables $\{i:u[i]=1\}$), then Winnow run with $\eta=1/4$ makes
--   $$|\mathcal M|\le 8k\log d$$
--   mistakes.
--
--   Compared with the Perceptron's $4(d+1)k$ on the same problem, the dependence on the dimension is logarithmic rather than linear.
--
--   **Formalization Note** Winnow is the corrected algorithm (update $w_{t+1}[i]=w_t[i]e^{2\eta y_tx_t[i]}$; the paper prints the opposite sign, under which the theorem is false — see the Winnow definition). Three hypotheses the page leaves implicit are explicit: $\eta>0$ (Winnow's parameter), $\eta<1/2$ (at $\eta=1/2$ the factor $1/(1-2\eta)$ is undefined), and $k\ge1$ (the theorem fails for $k=0$: $u=0$, $d=2$, $x_t=(1,1)$, $y_t=-1$ satisfies the margin condition, yet the first round is an error). $\|u\|_1$ is $\sum_i u[i]$. The particular case is about the run with $\eta=1/4$ (`winnowMistakes d (1/4) …`), a different run from the general one, and its margin condition is required on the $T$ rounds considered. $\log$ is natural. The sequence hypotheses are stated for all rounds; rounds are numbered $0,\dots,T-1$.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 174, Theorem 3.10 (proof pp. 174–175)

import Mathlib
import Definitions.Def_OnlineLearningOCO_Winnow_Winnow
open Finset

namespace OnlineLearningOCO.Winnow

/-- Theorem 3.10 (p. 174). Winnow with parameter `0 < η < 1/2` on instances `x_t ∈ {0,1}^d` and
labels `y_t ∈ {-1, 1}`; `M` is the set of rounds on which it errs and
`f_t(w) = 1[t ∈ M] [1 - y_t (2⟨w, x_t⟩ - 1)]_+`. For every `u ∈ {0,1}^d` with `‖u‖₁ = k ≥ 1`,
`|M| ≤ ∑_t f_t(w_t) ≤ (1/(1 - 2η)) (∑_t f_t(u) + k log(d)/η)`;
and if `y_t (2⟨u, x_t⟩ - 1) ≥ 1` for all `t`, the run with `η = 1/4` has `|M| ≤ 8 k log d`.
Rounds `0, …, T-1` stand for the paper's `1, …, T`. -/
theorem theorem_3_10 (d k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2)
    (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (u : Fin d → ℝ) (hu : ∀ i, u i = 0 ∨ u i = 1) (hu1 : ∑ i, u i = (k : ℝ)) (T : ℕ) :
    ((winnowMistakes d η x y T).card : ℝ) ≤
        ∑ t ∈ range T, winnowSurrogate d η x y t (winnowWeights d η x y t) ∧
    ∑ t ∈ range T, winnowSurrogate d η x y t (winnowWeights d η x y t) ≤
        (1 / (1 - 2 * η)) *
          (∑ t ∈ range T, winnowSurrogate d η x y t u + (k : ℝ) * Real.log d / η) ∧
    ((∀ t < T, 1 ≤ y t * (2 * ∑ i, u i * x t i - 1)) →
      ((winnowMistakes d (1 / 4) x y T).card : ℝ) ≤ 8 * (k : ℝ) * Real.log d) := by sorry

end OnlineLearningOCO.Winnow
