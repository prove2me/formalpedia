-- Prove2me | Theorems.Thm_FriedgutCoalition_claim_4_4
-- name    : FriedgutCoalition.claim_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:33:28.885569+00:00
-- url     : https://prove2.me/theorems/3855c262-8592-40af-8c57-d754edad8060
-- title:
--   Claim 4.4 — $i/r\le(1-p)^{\chi(i)}\le(i/r)(1+2p)$
-- statement:
--   Let $p\in(0,1/2)$ and $i\in[r]$, and let $\chi(i)$ be the nonnegative integer with
--
--   $$(1-p)^{\chi(i)+1}<\frac ir\le(1-p)^{\chi(i)}.\qquad(2)$$
--
--   Then
--
--   $$\frac ir\le(1-p)^{\chi(i)}\le\frac ir(1+2p).$$
--
--   The exponents $\chi(i)$ are the multiplicities of the selector sequence built in the proof of Lemma 4.3, and the claim is the estimate that gives its $2p$ error.
--
--   Differences from the source:
--   - encoding: χ(i), the unique nonnegative integer satisfying (2) → any k : ℕ satisfying (2); reason: (2) determines χ(i) uniquely, so the claim about every such k is the claim about χ(i)
--   - encoding: i ∈ [r] → a natural number i with 1 ≤ i ≤ r; reason: Lean convention; the same values
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Claim 4.4, p.12, with eq. (2) (standing assumption p ∈ (0,1/2) of §4, p.10)

import Mathlib

namespace FriedgutCoalition

/-- **Claim 4.4** (Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.12, with eq. (2)). Let `p ∈ (0, 1/2)` and
`i ∈ [r]`, and let `χ(i)` be the nonnegative integer with `(1 − p)^{χ(i)+1} < i/r ≤ (1 − p)^{χ(i)}`
(eq. (2)). Then `i/r ≤ (1 − p)^{χ(i)} ≤ (i/r)(1 + 2p)`.

**Formalization Note.** `χ(i)` is replaced by any `k ∈ ℕ` satisfying eq. (2); (2) determines it
uniquely, so this is the same claim. `i ∈ [r]` is `1 ≤ i ≤ r` for a natural number `i`. -/
theorem claim_4_4 (r : ℕ) (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) (i : ℕ) (hi1 : 1 ≤ i)
    (hir : i ≤ r) (k : ℕ)
    (hk : (1 - p) ^ (k + 1) < (i : ℝ) / r ∧ (i : ℝ) / r ≤ (1 - p) ^ k) :
    (i : ℝ) / r ≤ (1 - p) ^ k ∧ (1 - p) ^ k ≤ (i : ℝ) / r * (1 + 2 * p) := by sorry

end FriedgutCoalition
