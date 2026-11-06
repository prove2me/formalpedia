-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_4_6
-- name    : MinorityDynamics.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:42.158958+00:00
-- url     : https://prove2.me/theorems/99120793-b4c7-4917-93d4-a23a4049de43
-- title:
--   Lemma 4.6 — contraction in one step, total weight ≤ L, minimum weight ≥ 1/(2n)
-- statement:
--   Assume $k\ge L^{21/10}$ and $k=n^{o(1)}$ ($n,k$ odd, $n$ large). Then:
--
--   1. for every surviving state $y\in\mathcal S$, $(wQ)(y)\le\Big(1-\dfrac{1}{9D}\Big)w(y)$ (4.12);
--   2. $\sum_{x\in\mathcal S}w(x)\le L$;
--   3. $w(x)\ge\dfrac1{2n}$ for every $x\in\mathcal S$.
--
--   Here $w$ are the final weights (4.7) and $Q$ the matrix (4.1) of the auxiliary chain killed on $\mathcal H$. Iterating (4.12) bounds $\Pr_x(\tau'_{\mathcal H}>t)$ by $2nL(1-\frac1{9D})^t$.
--
--   Differences from the source:
--   - encoding: under (3.1): k ≥ L^{21/10}, k = n^{o(1)}; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N and odd k with (ln n)^{21/10} ≤ k ≤ n^ε; reason: equivalent to the reading "for every sequence k(n) = n^{o(1)}, for all sufficiently large n" (a sequence violating the ε-form infinitely often can be built from counterexamples with k ≤ n^{1/i}); same instances
--   - encoding: states x ∈ Ω = {0, 1/n, …, (n−1)/(2n)} → minority counts s ∈ Fin (n+1) with 2s < n, and x = s/n; reason: Lean convention for the finite state space; same instances
--   - encoding: min_{x∈S} w(x) ≥ 1/(2n) → w(x) ≥ 1/(2n) for every x ∈ S; reason: same content; avoids a junk value of the minimum of an empty family
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 4.6, p.19, (4.12)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_MinorityDynamics_Weights

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 4.6 (Contraction in one step)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.19 = PDF p.21), under (3.1):
"For every state y ∈ S, (wQ)(y) ≤ (1 − 1/(9D)) w(y). (4.12) Moreover, ∑_{x∈S} w(x) ≤ L and
min_{x∈S} w(x) ≥ 1/(2n)."

All three clauses: the one-step contraction (4.12) of the final weights `w` (4.7) under the
stopped auxiliary chain `Q` (4.1), the total-weight bound, and the minimum-weight bound.

**Formalization Note** "min_{x∈S} w(x) ≥ 1/(2n)" is stated as `w(x) ≥ 1/(2n)` for every `x ∈ S`.
"Under (3.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε`. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_4_6 :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k →
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
      (∀ s : Fin (n + 1), s ∈ Sset n k →
        wQ n k s ≤ (1 - 1 / (9 * DD n k)) * wFinal n k (((s : ℕ) : ℝ) / n)) ∧
      ∑ s ∈ SFin n k, wFinal n k (((s : ℕ) : ℝ) / n) ≤ logN n ∧
      (∀ s : Fin (n + 1), s ∈ Sset n k → 1 / (2 * (n : ℝ)) ≤ wFinal n k (((s : ℕ) : ℝ) / n)) := by sorry

end MinorityDynamics
