-- Prove2me | Theorems.Thm_LowAccLTC_claim_2_1_johnson_bound
-- name    : LowAccLTC.claim_2_1_johnson_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:39.837978+00:00
-- url     : https://prove2.me/theorems/f80e86e1-1d62-4f4f-a413-e07432177f29
-- title:
--   Claim 2.1 (Johnson's bound) — at most $1/\sqrt x$ codewords are $(1-2\sqrt x)$-close
-- statement:
--   Let $C\subseteq\Sigma^n$ be a code over a finite alphabet with distance $\delta\ge1-x$, where $0<x\le1/4$, distances being relative Hamming distances. Then for every $g\in\Sigma^n$,
--   $$\#\{c\in C:\ \mathrm{dist}(c,g)\le 1-2\sqrt x\}\ \le\ \frac{1}{\sqrt x}.$$
--   Equivalently, for $\varepsilon>0$: whenever $\delta\ge1-\varepsilon^2/4$, at most $2/\varepsilon$ codewords are at distance at most $1-\varepsilon$ from $g$.
--
--   The second form bounds the lists of local candidates in Lemma 4.3 (by $6/\varepsilon$ with $\delta\ge1-\varepsilon^2/36$).
--
--   Differences from the source:
--   - encoding: 'whenever δ ≥ 1 − ε²/4' (range of ε not stated) → 0 < ε; reason: ε > 0 is implicit in 2/ε; no upper bound is imposed (for ε > 1 no word is at distance ≤ 1 − ε < 0)
--   - encoding: distance δ of C → every two distinct codewords are at relative Hamming distance ≥ 1 − x (resp. 1 − ε²/4); reason: lower-bound semantics of 'distance δ ≥ …'
--   - encoding: an alphabet Σ → a Fintype A with decidable equality; counts are Set.ncard; reason: alphabets are finite
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Claim 2.1, p.13 (PDF p.16); proof Appendix A, p.78 (PDF p.81)

import Mathlib

namespace LowAccLTC

/-- **Claim 2.1** (Johnson's bound; Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.13 = PDF p.16).

Let `C ⊆ Σⁿ` be a code with distance `δ ≥ 1 - x`, where `0 < x ≤ 1/4`. Then for every `g ∈ Σⁿ`
at most `1/√x` codewords are `(1 - 2√x)`-close to `g`. Restated: whenever `δ ≥ 1 - ε²/4`
(`0 < ε`), at most `2/ε` codewords are at distance at most `1 - ε` from `g`. Distances are
relative Hamming distances.

**Formalization Note.** The page leaves the range of `ε` open; `ε > 0` is implicit in `2/ε`. No
upper bound on `ε` is imposed: for `ε > 1` no word is at distance at most `1 - ε < 0`, so the
clause holds trivially there. -/
theorem claim_2_1_johnson_bound {A : Type*} [Fintype A] [DecidableEq A] (n : ℕ)
    (C : Set (Fin n → A)) :
    (∀ x : ℝ, 0 < x → x ≤ 1 / 4 →
      (∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
        1 - x ≤ ((Finset.univ.filter (fun i => c i ≠ c' i)).card : ℝ) / n) →
      ∀ g : Fin n → A,
        ({c | c ∈ C ∧ ((Finset.univ.filter (fun i => c i ≠ g i)).card : ℝ) / n ≤
          1 - 2 * Real.sqrt x}.ncard : ℝ) ≤ 1 / Real.sqrt x) ∧
    (∀ ε : ℝ, 0 < ε →
      (∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
        1 - ε ^ 2 / 4 ≤ ((Finset.univ.filter (fun i => c i ≠ c' i)).card : ℝ) / n) →
      ∀ g : Fin n → A,
        ({c | c ∈ C ∧ ((Finset.univ.filter (fun i => c i ≠ g i)).card : ℝ) / n ≤ 1 - ε}.ncard : ℝ)
          ≤ 2 / ε) := by sorry

end LowAccLTC
