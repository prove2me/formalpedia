-- Prove2me | Theorems.Thm_MultiSecretary_NonAdaptive_dr_gap
-- name    : MultiSecretary.NonAdaptive.dr_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:03:36.932135+00:00
-- url     : https://prove2.me/theorems/d28ddebf-fc1e-401a-b6f0-f25088d98f9a
-- title:
--   Proposition 6 — 0 ≤ DR − V*_off ≤ M√n on T, and ≤ a₁m/(4ϵ′) when k/n is ϵ′ away from the jump points
-- statement:
--   Let $0<a_m<\dots<a_1$ and $\epsilon>0$. There is a constant $M=M(\epsilon,m,a_m,\dots,a_1)$ such that for all masses $f_j>0$ summing to one with $\tfrac12\min_jf_j=\epsilon$:
--
--   1. for all $0\le k\le n$,
--   $$0\le DR(n,k)-V^*_{\mathrm{off}}(n,k)\le M\sqrt n;$$
--   2. for every $0<\epsilon'<\epsilon$ and every $(n,k)$ in
--   $$\mathcal T'=\{(n,k)\in\mathcal T:\ \bar F(a_j)+\epsilon'\le k/n\le\bar F(a_{j+1})-\epsilon'\text{ for some }j\in[m]\},$$
--   $$0\le DR(n,k)-V^*_{\mathrm{off}}(n,k)\le\frac{a_1m}{4\epsilon'}.$$
--
--   Benchmarking against the deterministic relaxation costs at most $O(\sqrt n)$ in general, and only a constant when $k/n$ stays away from the jump points of $\bar F$.
--
--   **Formalization Note** Lean index $j\in\{0,\dots,m-1\}$ is the paper's index $j+1$, so `a 0` is the largest value $a_1$, `f 0` is $f_1$ and `f (Fin.rev 0)` is $f_m$. The second part assumes $n\ge1$ so that $k/n$ is the paper's ratio; $\bar F(a_{j+1})$ with $j=m$ is $\bar F(a_{m+1})=1$, which `Fbar f m` returns.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Appendix D, Proposition 6, p. 40

import Mathlib
import Definitions.Def_MultiSecretary_NonAdaptive_Model

namespace MultiSecretary.NonAdaptive

open Finset

/-- Proposition 6 (p. 40): there is `M ≡ M(ϵ, m, a)` with `0 ≤ DR - V*_off ≤ M√n` on `T`, and
`0 ≤ DR - V*_off ≤ a_1 m/(4ϵ')` on `T' = {F̄(a_j) + ϵ' ≤ k/n ≤ F̄(a_{j+1}) - ϵ' for some j}`,
`0 < ϵ' < ϵ`. -/
theorem dr_gap (ε : ℝ) (hε : 0 < ε) (m : ℕ) [NeZero m] (a : Fin m → ℝ) (ha : IsValues a) :
    ∃ M : ℝ, ∀ f : Fin m → ℝ, IsMasses f → eps f = ε →
      (∀ n k : ℕ, k ≤ n →
        0 ≤ DR a f n k - Voff a f n k ∧ DR a f n k - Voff a f n k ≤ M * Real.sqrt n) ∧
      (∀ ε' : ℝ, 0 < ε' → ε' < ε → ∀ n k : ℕ, 0 < n → k ≤ n →
        (∃ j : Fin m, Fbar f j.val + ε' ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ Fbar f (j.val + 1) - ε') →
        0 ≤ DR a f n k - Voff a f n k ∧
          DR a f n k - Voff a f n k ≤ a 0 * m / (4 * ε')) := by sorry

end MultiSecretary.NonAdaptive
