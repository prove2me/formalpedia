-- Prove2me | Theorems.Thm_KnapsackFPRAS_lemma_4_3
-- name    : KnapsackFPRAS.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:32.996799+00:00
-- url     : https://prove2.me/theorems/428c787f-3981-4eb0-8939-115b39ca2251
-- title:
--   Lemma 4.3 — $Z_a\le K_ZZ_w$ with probability at least $1-5\cdot10^{-5}$
-- statement:
--   There is an absolute constant $K_Z$ with the following property. Assume $1\le w_i\le T$ for all $i$ and $\sum_i w_i>T$ (the standing assumption (7)), let $B=2^b$ with $b\ge1$ and $S=T/B$, and let $\lambda\ge0$ be a tilt with $\lambda S\le1/10$ and $\mathbb E_{X\sim Q^\lambda_w}[w(X)]\le2T$. Then, over the random rounding $a$,
--
--   $$
--   \Pr\bigl[Z^\lambda_a\le K_Z\,Z^\lambda_w\bigr]\ge1-5\cdot10^{-5},
--   $$
--
--   where $Z^\lambda_v=\prod_i(1+e^{-\lambda v_i})$.
--
--   The comparison of the normalizers is what allows bounds proved for the rounded tilted distribution $Q_a$ to be converted into counts of feasible subsets of the original instance (Lemma 4.4).
--
--   Differences from the source:
--   - reading: for a sufficiently large absolute constant K_Z → ∃ K_Z chosen before n, w, T, B, λ; reason: the event grows with K_Z, so the two readings are equivalent
--   - reading: the lemma as printed in §4 → hypotheses 1 ≤ wᵢ ≤ T and T < ∑ wᵢ; reason: standing assumption (7) of §2 (p.9)
--   - generalization: λ the tilt of Lemma 3.2 and B of (14), with (15) → any λ ≥ 0 with λS ≤ 1/10 and E_{X∼Q^λ_w}[w(X)] ≤ 2T, any B = 2^b, b ≥ 1; reason: these are the properties the proof uses
--   - encoding: probability over the initial item rounding → the measure of the event under the product law Rounding.roundLaw B T w; reason: same probability
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Lemma 4.3, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_KnapsackFPRAS_Tilt
import Definitions.Def_KnapsackFPRAS_Rounding

set_option autoImplicit false

namespace KnapsackFPRAS

open MeasureTheory

/-- **Lemma 4.3**, p.17. "For a sufficiently large absolute constant 𝐾_𝑍, we have
𝑍_𝑎 ≤ 𝐾_𝑍 𝑍_𝑤 with probability at least 1 − 5·10⁻⁵ over the initial item rounding."

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Lemma 4.3, p.17 (PDF p.18).

**Formalization Note.** `K_Z` is one absolute constant chosen before everything else (the event
grows with `K_Z`, so "for a sufficiently large `K_Z`" and "for some `K_Z`" are equivalent). The
context of §4 enters as hypotheses: (7); `B = 2^b`, `b ≥ 1`; a tilt `λ ≥ 0` with
`λS ≤ 1/10` (from (15)) and `E_{X∼Q^λ_w}[w(X)] ≤ 2T` (Lemma 3.2). The probability is under
the product law `Rounding.roundLaw B T w` of the rounded vector `a`. -/
theorem lemma_4_3 :
    ∃ K_Z : ℝ, ∀ (n : ℕ) (w : Fin n → ℕ) (T : ℕ),
      (∀ i, 1 ≤ w i ∧ w i ≤ T) → T < ∑ i, w i →
      ∀ (b B : ℕ), 1 ≤ b → B = 2 ^ b →
      ∀ lam : ℝ, 0 ≤ lam → lam * Rounding.S B T ≤ 1 / 10 →
      Tilt.expWeight (fun i => (w i : ℝ)) lam ≤ 2 * T →
      1 - 5 / 100000 ≤ (Rounding.roundLaw B T w).real
        {a | Tilt.Z a lam ≤ K_Z * Tilt.Z (fun i => (w i : ℝ)) lam} := by sorry

end KnapsackFPRAS
