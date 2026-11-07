-- Prove2me | Theorems.Thm_LaconicBarrier_lemma_4_36
-- name    : LaconicBarrier.lemma_4_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:07.446846+00:00
-- url     : https://prove2.me/theorems/1534a7ed-73ff-4e96-b882-025bdca93fdf
-- title:
--   Lemma 4.36 — $k$-wise independent hash families with short seeds
-- statement:
--   For every $R, b, k \ge 1$ there is a $k$-wise independent family of hash functions $h : \{0,1\}^R \to \{0,1\}^b$ (Definition 4.35) with seed length $k \cdot \max\{R, b\}$ and evaluation time $\mathrm{poly}(R, b, k)$.
--
--   The verifier of the two-round protocol for the complement samples such hash functions to cut the set of consistent random tapes into buckets of bounded size.
--
--   Differences from the source:
--   - encoding: evaluation time poly(R, b, k) → one machine evaluates h_s(x) from (1^R, 1^b, 1^k, s, x) for all R, b, k within (R + b + k + 2)^d steps, d chosen before R, b, k; reason: a uniform algorithm, as the lemma is used; a machine per (R, b, k) would make the bound vacuous
--   - encoding: algorithms in an unspecified machine model ('polynomial time', 'T-time', 'verifier time') → one uniform deterministic two-tape oracle machine (KarpLiptonOM.OracleTM, empty oracle) per algorithm, on tuple-encoded inputs, coins as an extra input; reason: the paper names no machine model; every bound in this statement is polynomially robust
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Lemma 4.36, p.29 (PDF p.32)

import Mathlib
import Definitions.Def_LaconicBarrier_IsKWiseHash
import Definitions.Def_LaconicBarrier_RunsWithin

namespace LaconicBarrier

/-- **Lemma 4.36** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Lemma 4.36, p.29, after [Vad12, Corollary 3.34]): for every `R, b, k ≥ 1`
there is a `k`-wise independent family of hashes `h : {0,1}^R → {0,1}^b` with seed length
`k · max{R, b}` and evaluation time `poly(R, b, k)`.

**Formalization Note** The evaluation time is uniform: one machine evaluates `h_s(x)` from
`(1^R, 1^b, 1^k, s, x)` for every `(R, b, k)` within `(R + b + k + 2)^d` steps, with `d` chosen
before `R, b, k`. -/
theorem lemma_4_36 : ∃ (M : KarpLiptonOM.OracleTM) (d : ℕ), ∀ R b k : ℕ, 1 ≤ R → 1 ≤ b → 1 ≤ k →
    ∃ h : (Fin (k * max R b) → Bool) → (Fin R → Bool) → (Fin b → Bool), IsKWiseHash h k ∧
      ∀ s x, RunsWithin M [unary R, unary b, unary k, bits s, bits x] (bits (h s x))
        ((R + b + k + 2) ^ d) := by sorry

end LaconicBarrier
