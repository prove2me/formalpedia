-- Prove2me | Theorems.Thm_MonoIncExtrap_lemma_7
-- name    : MonoIncExtrap.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:17.063209+00:00
-- url     : https://prove2.me/theorems/c5e541d7-e55b-487c-a0fe-d74d3b4ab9b1
-- title:
--   Lemma 7, p.17 — the line search terminates, with a bound on $n_t$
-- statement:
--   Assume the standing assumptions of §2: $\gamma_0>0$, $\delta\in(0,1)$, $0<\nu\le1/2$, $\eta\in[0,\nu/(1+\nu))$, $\epsilon>0$, $x^0\in\mathrm{dom}\,B$, Assumption 1 with $\mu>0$, and let $x^*$ be the solution of (1). Let $M=\lceil\log(\xi/(\gamma_0L_{\widehat{\mathcal S}}))/\log\delta\rceil_+$ with $\xi=\nu(1-\eta)-\eta$. If $x^{t-1},x^t\in\mathcal S$ for some $t\ge1$ and Algorithm 1 has not terminated at iteration $t-1$, then $x^{t+1}$ is successfully generated at iteration $t$: the smallest integer $n_t$ passing the line search (6) exists, and
--   $$
--   n_t\le M+t-\sum_{i=1}^{t-1}n_i.
--   $$
--
--   This bounds the backtracking of the line search cumulatively, not per iteration.
--
--   **Formalization Note** Here $t=s+1$.
--
--   Differences from the source:
--   - encoding: $F$ is a point-valued operator on $\mathrm{cl}(\mathrm{dom}\,B)$ → a total map on $\mathbb R^n$, constrained only on $\mathrm{cl}(\mathrm{dom}\,B)$; reason: values of $F$ elsewhere never enter $F+B$ or a run, since iterates lie in $\mathrm{dom}\,B$
--   - encoding: Assumption 1(d), the resolvent of $\gamma B$ can be exactly evaluated → a family $J$ with $J_\gamma=(I+\gamma B)^{-1}$ for every $\gamma>0$; reason: the assumption has no mathematical content; the family exists and is unique on $\gamma>0$
--   - encoding: $n_t\le M+t-\sum_{i=1}^{t-1}n_i$ → $n_t+\sum_{i=1}^{t-1}n_i\le M+t$ in `ℕ`; reason: the same inequality, without natural-number subtraction
--   - encoding: has not terminated at iteration $t-1$, $t\ge1$ → `IsPrefix` at $t-1$ and the test (7) failed at $t-1$ when $t\ge2$; reason: iterations before $t-1$ did not terminate by `IsPrefix`, and at $t=1$ there is no earlier iteration
--   - encoding: $\lceil\omega\rceil_+$ → `Nat.ceil`; reason: $(\lceil\omega\rceil)_+$ is the natural-number ceiling, for every real $\omega$
--   - generalization: $L_{\mathcal S},L_{\widehat{\mathcal S}}$ are the constants given by Lemma 1, for some choice → every pair valid in the sense of Lemma 1; reason: the proof uses only the two Lipschitz bounds, and Lemma 1 supplies such a pair, so the printed statement is the instance at that pair
-- source:
--   Lu & Mei, Primal-dual extrapolation methods for monotone inclusions under local Lipschitz continuity, arXiv:2206.00973v3, Lemma 7, p.17

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting
import Definitions.Def_MonoIncExtrap_Algorithm1

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoIncExtrap

/-- **Lemma 7.** arXiv:2206.00973v3, Lemma 7, p.17. If `x^{t−1}, x^t ∈ S` and Algorithm 1 has not
terminated at iteration `t − 1`, then `x^{t+1}` is successfully generated at iteration `t`, i.e. a
smallest accepted integer `n_t` exists, and `n_t ≤ M + t − Σ_{i=1}^{t−1} n_i`.

**Formalization Note.** Here `t = s + 1`, the bound is written `n_t + Σ_{i=1}^{t−1} n_i ≤ M + t`
to avoid natural-number subtraction, and `M` is built from any valid pair of Lemma 1. -/
theorem lemma_7 {n : ℕ}
    {B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))}
    {I : Alg1.Input (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hI : Alg1.Standing B I xstar)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {γ : ℕ → ℝ} {n' : ℕ → ℕ} {s : ℕ}
    (hx : Alg1.IsPrefix I x γ n' s)
    (hstop : 1 ≤ s → ¬ Alg1.StoppedAt I x γ s)
    (hs : x s ∈ Alg1.setS B xstar (I.r0 xstar) I.ν)
    (hs' : x (s + 1) ∈ Alg1.setS B xstar (I.r0 xstar) I.ν)
    {LS LShat : ℝ} (hv : Alg1.ValidS B I xstar LS LShat) :
    ∃ m : ℕ, IsLeast {m | I.Accepts (x s) (x (s + 1)) (γ s) m} m ∧
      m + ∑ i ∈ Finset.Icc 1 s, n' i ≤ I.Mconst LShat + (s + 1) := by sorry

end MonoIncExtrap
