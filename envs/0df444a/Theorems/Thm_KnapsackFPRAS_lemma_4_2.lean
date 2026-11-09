-- Prove2me | Theorems.Thm_KnapsackFPRAS_lemma_4_2
-- name    : KnapsackFPRAS.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:12.191564+00:00
-- url     : https://prove2.me/theorems/c7b878d2-8a94-4ff9-8ce5-dfd143b71d54
-- title:
--   Lemma 4.2 — $\bar k_m=\sum_{i\in I_m}p^a_i=O(m)$
-- statement:
--   There is an absolute constant $C_1$ with the following property. Assume $1\le w_i\le T$ for all $i$ and $\sum_i w_i>T$ (the standing assumption (7)), let $B=2^b$ with $b\ge1$ and $S=T/B$, and let $\lambda\ge0$ be a tilt with $\lambda S\le1/10$ and $\mathbb E_{X\sim Q^\lambda_w}[w(X)]\le2T$. Then almost surely over the random rounding $a$, for every ordinary weight class $I_m$, $m\in\{2,4,\dots,B^2\}$,
--
--   $$
--   \bar k_m := \sum_{i\in I_m}p^a_i \le C_1\,m,\qquad p^a_i=\frac{1}{1+e^{\lambda a_i}} .
--   $$
--
--   Here $\bar k_m=\mathbb E_{X\sim Q_a}[|X\cap I_m|]$ is the expected number of class-$m$ items in a subset drawn from the rounded tilted distribution; the bound keeps the counting tables compact.
--
--   Differences from the source:
--   - reading: k̄_m = O(m) → ∃ C₁ chosen before n, w, T, B, λ with k̄_m ≤ C₁·m; reason: O(m) with an absolute constant
--   - reading: the lemma as printed in §4 → hypotheses 1 ≤ wᵢ ≤ T and T < ∑ wᵢ; reason: standing assumption (7) of §2 (p.9)
--   - generalization: λ the tilt of Lemma 3.2 and B of (14), with (15) → any λ ≥ 0 with λS ≤ 1/10 and E_{X∼Q^λ_w}[w(X)] ≤ 2T, any B = 2^b, b ≥ 1; reason: these are the properties the proof uses; (15) gives λS ≤ κ^{-10} ≤ 1/10 for the paper's choices
--   - encoding: for the rounded weights a → almost surely under Rounding.roundLaw B T w; reason: finite support; same as every realization
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Lemma 4.2, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_KnapsackFPRAS_Tilt
import Definitions.Def_KnapsackFPRAS_Rounding

set_option autoImplicit false

namespace KnapsackFPRAS

open MeasureTheory

/-- **Lemma 4.2**, p.16. "For every ordinary weight class 𝐼_𝑚, we have k̄_𝑚 = O(𝑚)."
Here k̄_𝑚 := ∑_{𝑖∈𝐼_𝑚} 𝑝^𝑎_𝑖 = E_{𝑋∼𝑄_𝑎}[|𝑋 ∩ 𝐼_𝑚|] (p.16).

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Lemma 4.2, p.16 (PDF p.17).

**Formalization Note.** "O(m)" is one absolute constant `C₁` chosen before everything else. The
context of §4 enters as hypotheses: (7); `B = 2^b`, `b ≥ 1`; a tilt `λ ≥ 0` with
`λS ≤ 1/10` (implied by (15)) and `E_{X∼Q^λ_w}[w(X)] ≤ 2T` (Lemma 3.2). The bound holds for
almost every rounded vector `a` of `Rounding.roundLaw B T w` and every ordinary class
`m = 2^j`, `1 ≤ j ≤ 2b`; `p^a_i = Tilt.p a λ i`. -/
theorem lemma_4_2 :
    ∃ C₁ : ℝ, ∀ (n : ℕ) (w : Fin n → ℕ) (T : ℕ),
      (∀ i, 1 ≤ w i ∧ w i ≤ T) → T < ∑ i, w i →
      ∀ (b B : ℕ), 1 ≤ b → B = 2 ^ b →
      ∀ lam : ℝ, 0 ≤ lam → lam * Rounding.S B T ≤ 1 / 10 →
      Tilt.expWeight (fun i => (w i : ℝ)) lam ≤ 2 * T →
      ∀ᵐ a ∂(Rounding.roundLaw B T w), ∀ j : ℕ, 1 ≤ j → j ≤ 2 * b →
        ∑ i ∈ Rounding.classIdx T w ((2 : ℝ) ^ j), Tilt.p a lam i ≤ C₁ * (2 : ℝ) ^ j := by sorry

end KnapsackFPRAS
