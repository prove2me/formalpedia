-- Prove2me | Theorems.Thm_LocalSweepFT_claim_5_10
-- name    : LocalSweepFT.claim_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:42:43.51622+00:00
-- url     : https://prove2.me/theorems/43ad97d1-add4-451e-88f5-6a70429d7607
-- title:
--   Claim 5.10 — the barrier argument with steps of Hamming distance $\le\Delta$ and constant $c/(8\binom{d'}{2}\Delta)$
-- statement:
--   Let $d'\ge2$ and $d-d'\ge2$. There is $c\in(0,1)$ such that
--   1. (Claim 5.9) for all sufficiently large $n$, the barrier property holds with step bound $1$ and constant $c$;
--   2. for every $\Delta\ge1$ and all sufficiently large $n$, the barrier property holds with step bound $\Delta$ and constant
--   $$c'=\frac{c}{8\binom{d'}{2}\Delta}.$$
--   That is: for chains $x_1,\dots,x_t$ of the side-$n$ torus with $x_1$ trivial, consecutive chains at Hamming distance at most $\Delta$, and all syndrome components of size at most $c'n$, $[0]=[x_1]=\dots=[x_t]$.
--
--   Consecutive Pauli frames of a circuit with gates of arity at most $\Delta$ differ in at most $\Delta$ qubits, so this is the form used in the proof of the main theorem.
--
--   Differences from the source:
--   - encoding: standing assumption "Fix integers d, d′ satisfying d′, d − d′ ≥ 2" (p.4) → hypotheses 2 ≤ d′ and 2 ≤ d − d′; reason: the section's standing assumption is a hypothesis of each statement
--   - encoding: c is the constant of Claim 5.9 → one c for which Claim 5.9 holds and the Δ-version holds with c/(8·C(d′,2)·Δ); reason: stating the two together keeps the constant shared
--   - reading: "the claim still holds" (including "if n is sufficiently large") → for each Δ ≥ 1 there is a threshold n₀ (which may depend on Δ); reason: the proof needs 4·C(d′,2)·Δ·d′ ≤ cn/2
--   - generalization: x₁ is a trivial chain → x₁ ∈ im ∂⁻ (an X-stabilizer); reason: x₁ = 0 is a special case; the filling class of a stabilizer is [0]
--   - reading: [x_i] defined from one canonical filling per component (Def 5.7) → [x_i] = [0] for every small filling, together with the existence of one; reason: at least as strong as the canonical choice
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 5.10, p.43

import Mathlib
import Definitions.Def_LocalSweepFT_BarrierProp

namespace LocalSweepFT

/-- Claim 5.10, p.43 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). With `c` a constant of Claim 5.9, the conclusion of
Claim 5.9 still holds when consecutive chains are at Hamming distance at most `∆`, with the size
constant `c′ = c / (8·C(d′,2)·∆)`.

**Formalization Note.** Stated together with Claim 5.9 so that the same `c` is used: there is
`c ∈ (0, 1)` for which Claim 5.9 holds and, for every `∆ ≥ 1` and all sufficiently large `n`
(the threshold may depend on `∆`), `BarrierProp d d′ n ∆ (c / (8·C(d′,2)·∆))` holds. Standing
assumption `d′, d − d′ ≥ 2` (p.4). -/
theorem claim_5_10 (d d' : ℕ) (h1 : 2 ≤ d') (h2 : 2 ≤ d - d') :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ (∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → BarrierProp d d' n 1 c) ∧
      ∀ Δ : ℕ, 1 ≤ Δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        BarrierProp d d' n Δ (c / (8 * (d'.choose 2 : ℝ) * Δ)) := by sorry

end LocalSweepFT
