-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_theorem_1_3
-- name    : InterleavedUnitaryNOF.LowerBound.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:49.532299+00:00
-- url     : https://prove2.me/theorems/82c686b1-6069-46ab-b5b7-d937f9a5ada4
-- title:
--   Theorem 1.3 — randomized NOF lower bound
-- statement:
--   Fix any power-of-two dimension schedule $m(n)=\Theta(\sqrt{n/\log_2n})$ that fits the source encoding for all sufficiently large lengths. Let $F_n$ be Interleaved Unitary Product on three $n$-bit strings, with the exact two's-complement decoder, ten complex matrices in the stated order, near-unitary Frobenius promise $10^{-4}$, and trace thresholds $0.1$ and $0.9$.
--
--   There exist $c>0$ and $N\ge2$, chosen before the input length and the protocol, such that for every $n\ge N$ and every randomized public-coin interactive three-player NOF protocol $\Pi$ with error at most $1/3$ on each promised input,
--
--   $$\operatorname{cost}(\Pi)\ge c\left(\frac{n}{\log_2n}\right)^{1/32}.$$
--
--   Cost bounds the total number of actually communicated bits on every input and every public seed. The result permits arbitrary transcript-dependent speakers, arbitrary finite real public-coin weights, unrestricted local computation, and a free local final answer. No correctness requirement is imposed outside the promise. The constants may depend on the fixed schedule, but not on $n$ or $\Pi$.
--
--   Differences from the source:
--   - encoding: m is a fitting power-of-two Θ(√(n/log n)) choice → a schema over every eventually admissible dimension schedule; reason: this covers the entire choice class and fixes its Θ constants before lengths and protocols
--   - encoding: all public-coin interactive protocols with free local output → published operational trees with arbitrary finite real public laws and a transcript-dependent local output interface; reason: finite input spaces and bounded cost permit grouping public seeds by their finitely many deterministic behaviors; the explicit output announcement adds one bit only
--   - encoding: the Ω̃(n^(1/32)) statement on p.3 → uniform c,N and the exact Ω((n/log₂ n)^(1/32)) rate; reason: the source explicitly derives this rate on pp.9,11; constants precede n and the protocol
--   - encoding: undefined promise inputs and complex near-unitary matrices → Option Bool and the exact bit decoder, with all ten Frobenius promises; reason: both endpoints and all promised inputs are retained; the arbitrary small-length decoder convention is outside the eventual conclusion
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Theorem 1.3, printed p.3 = PDF p.3; exact rate §4 pp.9,11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_PromiseProtocols

namespace InterleavedUnitaryNOF.LowerBound

/-- Wang–Wu–Yang, submission #1513, Theorem 1.3, pp.3,9,11.
The constants may depend on the fixed dimension schedule, and precede n and Π.
Every promised complex near-unitary input and every finite public real law is included.
Local output is free, and the cost bounds actual executions on all inputs and seeds. -/
theorem theorem_1_3 (m : ℕ → ℕ) (hm : AdmissibleSchedule m) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ n ≥ N, ∀ P : LocalPublicProtocol n, ∀ t : ℕ,
        P.Correct (m n) ((1 : ℝ)/3) → P.Bounded t →
        c * Real.rpow ((n : ℝ) / Real.logb 2 n) ((1 : ℝ)/32) ≤ (t : ℝ) := by sorry

end InterleavedUnitaryNOF.LowerBound
