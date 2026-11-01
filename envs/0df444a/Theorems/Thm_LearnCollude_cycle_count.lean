-- Prove2me | Theorems.Thm_LearnCollude_cycle_count
-- name    : LearnCollude.cycle_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:08.835144+00:00
-- url     : https://prove2.me/theorems/3e80eac1-1877-48ee-b516-8513b53ac527
-- title:
--   §3.2, pp. 20, 47 — the number of cycles and of learning periods in $T$ periods
-- statement:
--   For a schedule $N_c=vc+w$: the number $s_{c+1}$ of periods in the first $c$ cycles lies between $C_1c^2$ and $C_2c^2$; the cycle $c_T$ containing period $T$ satisfies $c_T\le C\sqrt T$; and the first $T$ periods contain at most $CT^{4/5}$ periods of phases 1–4.
--
--   Moreover, for any coins and noise, at the start of phase 5 of cycle $c$ both counters satisfy
--   $$
--   n^{col},\ n^{com}\ \ge\ \sum_{l=1}^c\lfloor N_l^\alpha\rfloor.
--   $$
--   These are the deterministic counting facts behind the rate $T^{-1/5}$.
--
--   Differences from the source:
--   - reading: t_c = Σ_{i ≤ c} N_i with five phases → cycle c has length L_c = max(N_c, 8⌊N_c^α⌋); reason: the printed t_c overlaps when 8⌊N_c^α⌋ > N_c, e.g. v = 1, w = 0, c = 1; p. 43 says the fifth phase then has length zero; this changes finitely many cycles
--   - reading: phase 5 of unspecified parity → an odd phase 5 ends with the first period of a pair and no update, and the next pair of that arm uses the same counter; reason: (10) makes the update in the even periods only
--   - generalization: number of cycles O(√T) → also the quantitative forms of the same paragraph: first c cycles ≍ c², phases 1–4 take O(T^{4/5}) periods (p. 47), counters at the start of phase 5 (p. 20); reason: each is stated in the proof of Theorem 3; the first gives the printed claim
--   - encoding: (10): p̂_k^col, ω_k in the exploitation update and n^com = n^col + 1; Assumption 1.2: φ₂(p₁) ∈ (0, pmax₁) → p̂_i^col, ω_i, n^com = n^com + 1, and φ₂(p₁) ∈ (0, pmax₂); reason: typos of the print
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), §3.2, p. 20, and proof of Theorem 3, p. 47

import Mathlib
import Definitions.Def_LearnCollude_Policy

open Filter MeasureTheory Topology

namespace LearnCollude

/-- **The cycle count**, Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06), §3.2, p. 20, and proof
of Theorem 3, p. 47.

The number of periods in the first `c` cycles grows proportionally to `c²`; the cycle `c_T` containing
period `T` has `c_T ≤ C√T`; the first `T` periods contain at most `C T^{4/5}` periods of phases 1–4;
and, whatever the coins and the noise, at the start of phase 5 of cycle `c` both counters are at least
`Σ_{l ≤ c} ⌊N_l^α⌋`. -/
theorem cycle_count (S : Schedule) :
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ c : ℕ, 1 ≤ c →
      C₁ * (c : ℝ) ^ 2 ≤ S.s (c + 1) ∧ (S.s (c + 1) : ℝ) ≤ C₂ * (c : ℝ) ^ 2) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 1 ≤ T →
      (S.cycleOf T : ℝ) ≤ C * Real.sqrt T ∧
      (((Finset.Icc 1 T).filter fun t => S.phaseOf t ≠ Phase.exploit).card : ℝ) ≤
        C * (T : ℝ) ^ (4 / 5 : ℝ)) ∧
    (∀ (M : Model) (G : Gains M) (h₀ : Arm → Fin 2 → ℝ) (coin : Arm → Fin 2 → ℕ → ℝ)
      (eps : Fin 2 → ℕ → ℝ) (c : ℕ) (a : Arm), 1 ≤ c →
      ∑ l ∈ Finset.Icc 1 c, S.f l ≤ (run M G S h₀ coin eps (S.s c + 8 * S.f c)).cnt a) := by sorry

end LearnCollude
