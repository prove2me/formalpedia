-- Prove2me | Theorems.Thm_NonmonotoneSubmod_SmoothLS_sls_two_fifths
-- name    : NonmonotoneSubmod.SmoothLS.sls_two_fifths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:13:10.213699+00:00
-- url     : https://prove2.me/theorems/0fe875d0-7de1-4a62-abe2-da4626e27e0c
-- title:
--   Theorem 3.6 — Smooth Local Search runs in polynomial time and achieves $(\frac25 - \frac{9}{5n})OPT$
-- statement:
--   Let $f : 2^X \to \mathbb{R}$ be a nonnegative submodular function on a finite ground set $X$ with $n = |X| \ge 1$ elements, and $OPT = \max_{S \subseteq X} f(S)$. A **run** of Algorithm SLS (Smooth Local Search) with bias $\delta$ is a sequence of sets $A_0 = \emptyset, A_1, A_2, \dots$ such that, for each iteration $t$, estimates $\tilde\omega_t$ of the smoothed marginals $\omega_{A_t,\delta}$ are accurate within $\pm\frac{1}{n^2}OPT$, and $A_{t+1}$ arises from $A_t$ by step 3 (add some $x \notin A_t$ with $\tilde\omega_t(x) > \frac{2}{n^2}OPT$) or, if step 3 does not apply, by step 4 (remove some $x \in A_t$ with $\tilde\omega_t(x) < -\frac{2}{n^2}OPT$).
--
--   1. **Running time.** For every $\delta \in (0,1]$, every run of $k$ iterations with accurate estimates satisfies
--   $$
--   k < \frac{n^2}{\delta};
--   $$
--   for $\delta = 1/3$ this is fewer than $3n^2$ iterations.
--   2. **Approximation.** Let $\delta = 1/3$, and suppose the run has terminated at $A_k$ (neither step applies to the accurate estimates $\tilde\omega_k$). The algorithm returns $\mathcal{R}(A_k, \delta')$ with $\delta' = 1/3$ with probability $0.9$ and $\delta' = -1$ with probability $0.1$; its expected value satisfies
--   $$
--   \tfrac{9}{10}\, \mathbf{E}[f(\mathcal{R}(A_k, \tfrac13))] + \tfrac{1}{10}\, \mathbf{E}[f(\mathcal{R}(A_k, -1))] \ge \Big(\frac{2}{5} - \frac{9}{5n}\Big) OPT.
--   $$
--
--   This is the headline algorithmic result of the paper: a randomized local search on a smoothed potential gives a $2/5 - o(1)$ approximation for maximizing an arbitrary nonnegative submodular function in the value oracle model, improving the $1/3$ of deterministic local search.
--
--   **Formalization Note** This is the pinned-down form of the printed statement. "Runs in polynomial time" is the iteration bound $n^2/\delta$ established in the proof (p. 1143), stated for every $\delta \in (0,1]$ (the proof needs $\delta > 0$); the $o(1)$ is the explicit $\frac{9}{5n}$ of the proof's last line (p. 1144). Both are conditional on every estimate being accurate within $\pm\frac{1}{n^2}OPT$ (non-strict), which replaces the printed "with high probability"; the sampling that produces the estimates is not modelled. The thresholds $\pm\frac{2}{n^2}OPT$ use $OPT$ itself, as the proof does. $\mathcal{R}(A,-1)$ is the deterministic set $X \setminus A$, i.e. the proof's $f(B)$; it is written through the same bias-sampling definition as $\mathcal{R}(A, \tfrac13)$. $n \ge 1$ is assumed.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1142, Theorem 3.6; proof pp. 1142-1144 (iteration bound p. 1143, final line p. 1144)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample
import Definitions.Def_NonmonotoneSubmod_SmoothLS_SLSAlgorithm

namespace NonmonotoneSubmod.SmoothLS

/-- Theorem 3.6 (Feige–Mirrokni–Vondrák 2011, p. 1142; proof pp. 1142–1144), in the explicit form
of its proof. Let `f ≥ 0` be submodular on a ground set of `n = |X| ≥ 1` elements. A run of
Algorithm SLS is a sequence of sets `A 0 = ∅, A 1, …` where each `A (t+1)` arises from `A t` by
step 3 or step 4 applied to estimates `est t` of `ω_{A t, δ}` accurate within `± OPT/n²`.
1. (Running time.) For every bias `δ ∈ (0, 1]`, every run of `k` steps has `k < n²/δ`
   (for `δ = 1/3`: fewer than `3n²` iterations).
2. (Approximation.) For `δ = 1/3`, if the run has terminated at step `k`, the output
   `R(A k, δ′)` with `δ′ = 1/3` with probability `0.9` and `δ′ = -1` with probability `0.1` has
   expected value
   `0.9 E[f(R(A k, 1/3))] + 0.1 E[f(R(A k, -1))] ≥ (2/5 - 9/(5n)) OPT`. -/
theorem sls_two_fifths {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ (A : ℕ → Finset X) (est : ℕ → X → ℝ) (k : ℕ),
        A 0 = ∅ →
        (∀ t, t < k → Accurate f δ (A t) (est t)) →
        (∀ t, t < k → SLSStep f (est t) (A t) (A (t + 1))) →
        (k : ℝ) < (Fintype.card X : ℝ) ^ 2 / δ) ∧
    (∀ (A : ℕ → Finset X) (est : ℕ → X → ℝ) (k : ℕ),
        A 0 = ∅ →
        (∀ t, t ≤ k → Accurate f (1 / 3) (A t) (est t)) →
        (∀ t, t < k → SLSStep f (est t) (A t) (A (t + 1))) →
        SLSTerminated f (est k) (A k) →
        (2 / 5 - 9 / (5 * (Fintype.card X : ℝ))) * NonmonotoneSubmod.Shared.OPT f ≤
          9 / 10 * Phi f (1 / 3) (A k) + 1 / 10 * Phi f (-1) (A k)) := by sorry

end NonmonotoneSubmod.SmoothLS
