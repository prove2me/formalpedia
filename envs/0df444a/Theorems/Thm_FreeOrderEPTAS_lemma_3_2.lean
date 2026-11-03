-- Prove2me | Theorems.Thm_FreeOrderEPTAS_lemma_3_2
-- name    : FreeOrderEPTAS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:37.118895+00:00
-- url     : https://prove2.me/theorems/e7976ea3-3ee1-43f4-b009-b63c06b919ad
-- title:
--   Lemma 3.2 — (IPProphets) is feasible (corrected: guess grid, buckets)
-- statement:
--   Let $\sigma^*$ be optimal and $1/\epsilon$ a positive integer. For all guesses satisfying (14) and (15), (IPProphets) admits a feasible solution. Moreover, if $\epsilon<1$ and $E\in[(1-\epsilon)\mathrm{OPT},\mathrm{OPT}]$, then guesses satisfying (14) and (15) exist on the grid $\{k\epsilon^2E:0\le k\le\lceil1/(\epsilon^2(1-\epsilon))\rceil\}$.
--
--   This is why the enumeration of §3.3 reaches a feasible Santa Claus instance.
--
--   Differences from the source:
--   - correction: grid $\{0,\epsilon^2E,\dots,(1-\epsilon^2)E\}$, p.18 → grid $\{k\epsilon^2E:0\le k\le\lceil1/(\epsilon^2(1-\epsilon))\rceil\}$; reason: $\mathrm{BaseVal}$ can exceed $E$: $\epsilon=1/2$, $x=(1,0.9)$, $\sigma^*$ the identity, $E=0.5$, where (14) needs a guess in $[0.775,0.9]$, above the printed top $0.375$
--   - correction: jump iff the closed interval $[V^*_t,V^*_{t-1}]$ contains a multiple of $\epsilon V^*_1$; $B_2=\{X_{\sigma^*(T_K)}\}$, p.17 → jump variable at $s$ iff $(V^*_{s+1},V^*_s]$ contains a multiple; buckets as in Figure 1; reason: $\epsilon=1/2$, values $(1,0,0,0,0)$, $\sigma^*$ the identity: closed intervals give $K\ge4>1/\epsilon$; values $(1,0.6,0.6,0)$: the text’s stable bucket has step $0.6>\epsilon\mathrm{OPT}$, against Figure 1 and the proof of Claim 3.4
--   - encoding: times and buckets $1,\dots,n$ and $1,\dots,2K+1$ → 0-based `Fin n`, `Fin (2K+1)`; even index stable, odd index jump; reason: a shift of indices; same objects
--   - encoding: the guesses are read from the enumerated grid → non-negativity is a clause of `IsGuess`; reason: the grid is non-negative; p.20 uses "the non-negativity of BaseGuess"
--   - reading: $\mathrm{BaseVal}(B_{2K+2})$, needed in (15) for the top bucket, undefined → $V^*_1$ (`BaseVal` at the index $2K+1$); reason: the value (15) needs at the top bucket; it is $\mathrm{OPT}$ for optimal $\sigma^*$
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Lemma 3.2, p.19; (14), (15), p.18

import Mathlib
import Definitions.Def_FreeOrderEPTAS_IsGuess
import Definitions.Def_FreeOrderEPTAS_IPProphets
import Definitions.Def_FreeOrderEPTAS_OPT
import Definitions.Def_FreeOrderEPTAS_freeOrder

namespace FreeOrderEPTAS

/-- Lemma 3.2, p.19 (arXiv:2007.13121v3), for `σ*` optimal and `1/ϵ ∈ ℕ`: for guesses satisfying (14)
and (15), (IPProphets) admits a feasible solution. Also, when `E ∈ [(1 - ϵ) OPT, OPT]` with
`ϵ < 1`, such guesses exist on the corrected grid `{k ϵ²E : 0 ≤ k ≤ ⌈1/(ϵ²(1 - ϵ))⌉}`. -/
theorem lemma_3_2 {n : ℕ} (I : Instance n) (σs : Equiv.Perm (Fin n)) (hopt : V I σs = OPT I)
    (ϵ E : ℝ) (q : ℕ) (hq : 0 < q) (hϵ : ϵ = 1 / (q : ℝ)) :
    (∀ b Δ : Fin (2 * numJumps I σs ϵ + 1) → ℝ, IsGuess I σs ϵ E b Δ →
      IPProphetsFeasible I b Δ) ∧
    (ϵ < 1 → (1 - ϵ) * OPT I ≤ E → E ≤ OPT I →
      ∃ b Δ : Fin (2 * numJumps I σs ϵ + 1) → ℝ, IsGuess I σs ϵ E b Δ ∧
        ∀ i, b i ∈ guessGrid ϵ E ⌈1 / (ϵ ^ 2 * (1 - ϵ))⌉₊ ∧
          Δ i ∈ guessGrid ϵ E ⌈1 / (ϵ ^ 2 * (1 - ϵ))⌉₊) := by sorry

end FreeOrderEPTAS
