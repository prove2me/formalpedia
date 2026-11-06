-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_2_2
-- name    : MinorityDynamics.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:37.546424+00:00
-- url     : https://prove2.me/theorems/af67cbcc-ebca-41f7-9c59-5060b766424f
-- title:
--   Lemma 2.2 — one-step comparison: $d_{TV}\le n(3/4)^k\le 1/n$ outside $I_*$
-- statement:
--   Assume $k\ge 8L$ with $L=\ln n$, and $n$, $k$ odd and $n$ large enough. For every state $x\in\Omega\setminus I_*$, the total variation distance between the law of $X_1$ for the minority chain started at $x$ and the law of $X'_1$ for the auxiliary chain started at $x$ satisfies
--   $$d_{TV}\big(\mathcal L_x(X_1),\mathcal L_x(X'_1)\big)\le n(3/4)^k\le \frac1n .$$
--
--   Outside the central interval the auxiliary chain, whose update uses the explicit branches of $f$, is therefore an accurate one-step proxy for the actual chain.
--
--   Differences from the source:
--   - encoding: "all of our statements hold for sufficiently large n" (standing, p.2); n, k odd → ∃ N, ∀ odd n ≥ N, ∀ odd k; reason: the paper's standing convention written out; same instances
--   - encoding: states x ∈ Ω = {0, 1/n, …, (n−1)/(2n)} → minority counts s ∈ Fin (n+1) with 2s < n, and x = s/n; reason: Lean convention for the finite state space; same instances
--   - encoding: total variation distance between the laws → (1/2) ∑ |μ(s′) − ν(s′)| over minority counts; reason: equal to max over events for probability vectors; same value
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 2.2, p.12

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 2.2 (One-step comparison)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.12 = PDF p.14): "Suppose that k ≥ 8L. For all
x ∈ Ω \ I∗, given Xt = X′t = x, the total variation distance between the laws of Xt+1 and X′t+1 is
at most n(3/4)^k ≤ 1/n."

Both inequalities are part of the conclusion: for every state `x = s/n ∈ Ω` outside `I∗`, the total
variation distance between the minority-chain transition law and the auxiliary-chain (folded)
transition law from `x` is at most `n(3/4)^k`, and `n(3/4)^k ≤ 1/n`.

**Formalization Note** "For sufficiently large n" (p.2, standing) is `∃ N, ∀ n ≥ N`; `n`, `k` odd
(p.2). `L = ln n`. Laws are compared on minority counts `0, …, n`. -/
theorem lemma_2_2 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k → 8 * logN n ≤ (k : ℝ) →
      ∀ s : Fin (n + 1), InOmega n s → ((s : ℕ) : ℝ) / n ∉ Istar n k →
        tvDist (actualKernel n k s) (auxFoldedKernel n k s) ≤ (n : ℝ) * (3 / 4) ^ k ∧
          (n : ℝ) * (3 / 4) ^ k ≤ 1 / n := by sorry

end MinorityDynamics
