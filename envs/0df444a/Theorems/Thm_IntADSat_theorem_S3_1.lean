-- Prove2me | Theorems.Thm_IntADSat_theorem_S3_1
-- name    : IntADSat.theorem_S3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:14.119175+00:00
-- url     : https://prove2.me/theorems/9c23f7d2-8d62-4234-bbc7-9ba8a47539ff
-- title:
--   Theorem S3.1 — simultaneous irreducibility for growing primes
-- statement:
--   There is an absolute integer $P_0$ such that, for $G\sim G(n,1/2)$, with probability $1-\exp(-\Omega(\sqrt n))$ the pair $(A_G,D_G)$ has no nonzero proper common invariant subspace over $\mathbb F_p$, simultaneously for every prime $P_0\le p\le n$. Consequently
--
--   $$
--   M_p(G)=\mathbb F_p^n\qquad(P_0\le p\le n)
--   $$
--
--   on that same event.
--
--   Formally: there are $P_0\in\mathbb N$ and $c>0$ such that for all large $n$ the probability that some prime $p\in[P_0,n]$ admits a nonzero proper common invariant subspace is at most $\exp(-c\sqrt n)$, and every graph outside this event has $M_p(G)=\mathbb F_p^n$ for all primes $p\in[P_0,n]$.
--
--   Differences from the source:
--   - reading: with probability 1 − exp(−Ω(√n)) → ∃ c > 0, eventually failure probability ≤ exp(−c√n); reason: the meaning of exp(−Ω(√n))
--   - reading: Consequently M_p(G) = 𝔽_pⁿ (P₀ ≤ p ≤ n) on that same event → eventually in n, every graph outside the bad event has M_p full for all primes P₀ ≤ p ≤ n; reason: inclusion of events
--   - encoding: absolute integer P₀ → P₀ : ℕ; reason: a cutoff for primes; same content
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem S3.1, p.35 (PDF 36)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_wordModule
import Definitions.Def_IntADSat_HasProperInvariant

set_option autoImplicit false

namespace IntADSat

/-- **Theorem S3.1 (Simultaneous irreducibility in a growing interval)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.35 (PDF 36)). There is
an absolute integer `P₀` such that, for `G ∼ G(n, 1/2)`, with probability `1 − exp(−Ω(√n))` the pair
`(A_G, D_G)` has no nonzero proper common invariant subspace over `𝔽_p`, simultaneously for every prime
`P₀ ≤ p ≤ n`. Consequently `M_p(G) = 𝔽_pⁿ` (`P₀ ≤ p ≤ n`) on that same event.

**Formalization Note** `1 − exp(−Ω(√n))` is read as: there is `c > 0` with failure probability at most
`exp(−c√n)` for all large `n`; "on that same event" is the inclusion of events, stated for every graph. -/
theorem theorem_S3_1 :
    ∃ P₀ : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => ∃ p : ℕ, p.Prime ∧ P₀ ≤ p ∧ p ≤ n ∧ HasProperInvariant (ZMod p) G) ≤
        Real.exp (-c * Real.sqrt n) ∧
      ∀ G : SimpleGraph (Fin n),
        (¬ ∃ p : ℕ, p.Prime ∧ P₀ ≤ p ∧ p ≤ n ∧ HasProperInvariant (ZMod p) G) →
        ∀ p : ℕ, p.Prime → P₀ ≤ p → p ≤ n → wordModule (ZMod p) G = ⊤ := by sorry

end IntADSat
