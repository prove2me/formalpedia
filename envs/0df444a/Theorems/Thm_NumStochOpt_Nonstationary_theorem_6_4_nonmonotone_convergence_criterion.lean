-- Prove2me | Theorems.Thm_NumStochOpt_Nonstationary_theorem_6_4_nonmonotone_convergence_criterion
-- name    : NumStochOpt.Nonstationary.theorem_6_4_nonmonotone_convergence_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T19:33:29.315037+00:00
-- url     : https://prove2.me/theorems/91c03a19-da06-432d-bf94-6acd3f0d9ea5
-- title:
--   Theorem 6.4 — a convergence criterion for nonmonotone sequences
-- statement:
--   Let $X^* \subseteq \mathbb R^n$ be closed and let $(x^s)_{s \ge 0}$ be a sequence in $\mathbb R^n$ such that:
--
--   1. $x^s \in K$ for all $s$, with $K$ compact;
--   2. for every subsequence $(x^{s_k})$ with $\lim_k x^{s_k} = x'$:
--      - (a) if $x' \in X^*$, then $\|x^{s_k+1} - x^{s_k}\| \to 0$ as $k \to \infty$;
--      - (b) if $x' \notin X^*$, then for every sufficiently small $\varepsilon > 0$ and every $k$ the exit time
--      $$
--      \tau_k = \min\{s \ge s_k : \|x^s - x^{s_k}\| > \varepsilon\}
--      $$
--      is finite;
--   3. there is a continuous function $V : \mathbb R^n \to \mathbb R$ taking at most countably many values on $X^*$ such that, in the situation of (2)(b),
--   $$
--   \limsup_{k \to \infty} V(x^{\tau_k}) < \lim_{k \to \infty} V(x^{s_k}).
--   $$
--
--   Then the sequence $(V(x^s))$ converges, and every accumulation point of $(x^s)$ belongs to $X^*$.
--
--   The criterion replaces monotone decrease of a Lyapunov function by the requirement that the sequence leave any neighbourhood of a non-solution with a lower value of $V$; it applies to essentially nonmonotone procedures such as the nonstationary method (6.41), where Zangwill-type conditions are hard to verify. The book cites the proof to Ermoliev's 1976 monograph [5, p. 181].
--
--   **Formalization Note** The page prints (2)(b) as "$\tau_k = \min\{s \mid s \ge s_k, \|x^{s_k} - x^s\| < \varepsilon\} > \infty$", which no sequence satisfies. The proof of Theorem 6.3 (pp. 155–156) shows what is intended: $\tau_k$ is the first index from $s_k$ on with $\|x^s - x^{s_k}\| > \varepsilon$, and (2)(b) asserts $\tau_k < \infty$; that is the reading formalized. "For $\varepsilon$ sufficiently small and for any $s_k$" is read as: there is $\varepsilon_0 > 0$ such that for all $\varepsilon \in (0, \varepsilon_0)$ and all $k$; condition (3) is required for the same $\varepsilon$. The left-hand limit of (3) is read as a $\limsup$ (the proof of Theorem 6.3 prints $\overline{\lim}$); the right-hand limit exists and equals $V(x')$ by continuity of $V$, and is written so. The real $\limsup$ is well defined because $V$ is bounded on the compact set $K$. Subsequences are strictly increasing index maps $\varphi : \mathbb N \to \mathbb N$ with $s_k = \varphi(k)$; accumulation points are cluster points of the sequence along `atTop`.
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 155, Theorem 6.4 (citing Yu. Ermoliev, Methods of Stochastic Programming, Nauka 1976, p. 181)

import Mathlib
import Definitions.Def_NumStochOpt_Nonstationary_ExitTime

open Filter Topology

namespace NumStochOpt.Nonstationary

/-- Theorem 6.4 (Ermoliev, Ch. 6 of Ermoliev & Wets (1988), p. 155, citing [5, p. 181]): a
convergence criterion for nonmonotone sequences. Let `X* ⊆ ℝⁿ` be closed and `(x^s)` a sequence
in `ℝⁿ` such that
(1) all `x^s` lie in a compact set `K`;
(2) for every subsequence `x^{s_k} → x'`:
  (a) if `x' ∈ X*` then `‖x^{s_k+1} - x^{s_k}‖ → 0`;
  (b) if `x' ∉ X*` then for all sufficiently small `ε > 0` and every `k` the exit time
      `τ_k = min {s ≥ s_k | ‖x^s - x^{s_k}‖ > ε}` is finite, and
(3) for a continuous `V` taking at most countably many values on `X*`,
    `limsup_k V(x^{τ_k}) < lim_k V(x^{s_k}) = V(x')`.
Then `V(x^s)` converges and every accumulation point of `(x^s)` lies in `X*`.
The page prints `τ_k = min{s | s ≥ s_k, ‖x^{s_k} - x^s‖ < ε} > ∞`; the reading used is the
one the proof of Theorem 6.3 (pp. 155–156) verifies. -/
theorem theorem_6_4_nonmonotone_convergence_criterion {n : ℕ}
    (Xstar K : Set (EuclideanSpace ℝ (Fin n))) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hXstar : IsClosed Xstar)
    (hK : IsCompact K) (hxK : ∀ s, x s ∈ K)
    (h2a : ∀ (φ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin n)), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 x') → x' ∈ Xstar →
        Tendsto (fun k => ‖x (φ k + 1) - x (φ k)‖) atTop (𝓝 0))
    (hV : Continuous V) (hVcount : (V '' Xstar).Countable)
    (h2b3 : ∀ (φ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin n)), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 x') → x' ∉ Xstar →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          (∀ k, ∃ s, φ k ≤ s ∧ ε < ‖x s - x (φ k)‖) ∧
          limsup (fun k => V (x (exitTime x (φ k) ε))) atTop < V x') :
    (∃ L : ℝ, Tendsto (fun s => V (x s)) atTop (𝓝 L)) ∧
      ∀ x' : EuclideanSpace ℝ (Fin n), MapClusterPt x' atTop x → x' ∈ Xstar := by sorry

end NumStochOpt.Nonstationary
