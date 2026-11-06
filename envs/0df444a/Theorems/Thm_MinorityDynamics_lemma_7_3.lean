-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_7_3
-- name    : MinorityDynamics.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:09.473438+00:00
-- url     : https://prove2.me/theorems/1f673fc9-228c-447f-97e3-7216fa11dfff
-- title:
--   Lemma 7.3 — from small states to $I_*^{\mathrm{in}}$ in $d-1$ rounds, w.p. $1-n^{-\omega(1)}$
-- statement:
--   Assume (1.1) ($n,k$ odd, $n$ large), with $d$ the integer of the residue condition. For the auxiliary chain, uniformly over initial states $x\in\Omega$ with $1/n\le x\le K/n$,
--   $$\Pr_x\Big(X'_{d-1}\in I_*^{\mathrm{in}},\ 0<X'_t<a\ \text{for all }0\le t<d-1\Big)\ge 1-n^{-\omega(1)},$$
--   where $I_*^{\mathrm{in}}=[\frac32b,\frac23c]$. Precisely: for every $A>0$ the probability is at least $1-n^{-A}$ for all large $n$, uniformly in $k$, $d$ and $x$.
--
--   Differences from the source:
--   - encoding: under (1.1): k ≥ L^{21/10}, k = n^{o(1)}, 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20} for some d ∈ ℕ; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N, odd k and d ∈ ℕ with (ln n)^{21/10} ≤ k ≤ n^ε and 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20} (real quotient); reason: equivalent to the sequence reading of k = n^{o(1)} for all sufficiently large n; "for some d" in a hypothesis is "for every d" satisfying it; same instances
--   - encoding: states x ∈ Ω = {0, 1/n, …, (n−1)/(2n)} → minority counts s ∈ Fin (n+1) with 2s < n, and x = s/n; reason: Lean convention for the finite state space; same instances
--   - encoding: ≥ 1 − n^{−ω(1)}, uniformly over initial states → ∀ A > 0, ∃ ε > 0, ∃ N such that the probability is ≥ 1 − n^{−A} for every admissible n, k, d and initial state; reason: the definition of n^{−ω(1)} with the sequence reading of k = n^{o(1)}; same content
--   - encoding: the auxiliary chain X′_t → the chain on unfolded counts, started at R_0 = nx, with X′_t = min{R_t, n − R_t}/n; reason: same law
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 7.3, p.38

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 7.3 (From small states to I∗^in)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.38 = PDF p.40): "Assume (1.1). For the
auxiliary chain, uniformly over initial states x ∈ Ω with 1/n ≤ x ≤ K/n,
Pr_x( X′_{d−1} ∈ Iin∗, 0 < X′t < a for all 0 ≤ t < d − 1 ) ≥ 1 − n^{−ω(1)}."

**Formalization Note** `1 − n^{−ω(1)}`, uniformly over the initial states, is: for every `A > 0`
there are `ε`, `N` such that the probability is at least `1 − n^{−A}` for every admissible `n`, `k`,
`d` and every initial state. `d` is the integer of the residue condition (1.1). The chain is the
auxiliary chain with unfolded count as state, started at `R₀ = nx`; `X′ₜ = min{Rₜ, n − Rₜ}/n`.
"Assume (1.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`, `2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20}` for some `d ∈ ℕ`, with a real quotient `k^d/n`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε` and every `d` satisfying the residue condition. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_7_3 :
    ∀ A : ℝ, 0 < A → ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k →
      ∀ d : ℕ,
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
    2 * Real.log n ≤ (k : ℝ) ^ d / n → (k : ℝ) ^ d / n ≤ (1 / 5) * Real.log n ^ ((21 : ℝ) / 20) →
      ∀ s : Fin (n + 1), InOmega n s → 1 / (n : ℝ) ≤ ((s : ℕ) : ℝ) / n →
        ((s : ℕ) : ℝ) / n ≤ KK n k / n →
        1 - (n : ℝ) ^ (-A) ≤
          stayProb (auxKernel n k)
            (fun t => if t < d - 1 then {R | 0 < foldFrac n R ∧ foldFrac n R < aPt k}
              else {R | foldFrac n R ∈ IstarIn n k})
            (d - 1) s := by sorry

end MinorityDynamics
