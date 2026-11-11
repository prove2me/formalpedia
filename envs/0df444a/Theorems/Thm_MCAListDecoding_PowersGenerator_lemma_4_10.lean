-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_4_10
-- name    : MCAListDecoding.PowersGenerator.lemma_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:42.735349+00:00
-- url     : https://prove2.me/theorems/4927b4b0-ea63-41a1-b275-a37a6312729a
-- title:
--   Lemma 4.10 — a curve missing some bad seed has s_P ≥ Δ_C − γn, i.e. z_P ≤ 1 − δ_C + γ
-- statement:
--   Throughout §4 (p. 27) the standing hypotheses are $\gamma n \ge 1$, $2\gamma n < \Delta_C$ and $\gamma < J_{d+2}(\delta_C)$, with $\gamma n = e$ an integer. Let $P$ be a curve and suppose some seed of $B$ does not lie on $P$. Then
--   $$s_P\ge\Delta_C-\gamma n,\qquad\text{equivalently}\qquad z_P\le 1-\delta_C+\gamma.$$
--   Both forms are stated.
--
--   Differences from the source:
--   - encoding: radius γ ∈ [0,1] with γn an integer (convention (2), p. 27) → a natural number e (= γn) and the real radius e/n; e ≤ n is implied by 2e < Δ_C ≤ n; reason: the paper's integer-radius convention (2); every γ with γn ∈ {0,…,n} is e/n for e = γn
--   - encoding: a code C with minimum distance Δ_C (defined for codes with at least two codewords) → hypothesis C ≠ ⊥, with minDist C the minimum weight of a nonzero codeword; reason: Δ_C and δ_C are undefined for the zero code; the hypothesis only excludes that undefined case
--   - encoding: the unique codeword c_x within distance γn of u(x) (Lemma 4.2) → decoded C d e u x, a codeword within Hamming distance e of combinedWord d u x chosen by Classical.choose (0 if none); reason: under 2e < Δ_C the codeword is unique on bad seeds (Lemma 4.2), so it is the paper's c_x there
--   - encoding: Σ, [n] = {1,…,n}, words u_0,…,u_d → Alph, Fin n (0-based coordinates), u : Fin (d+1) → Fin n → Alph; reason: Lean naming and indexing conventions; no instance changes
--   - encoding: s_P ≥ Δ_C − γn → (minDist C : ℤ) − e ≤ (curveS u P : ℤ); reason: avoids truncated natural subtraction; the same inequality
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma 4.10, p. 29

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code
import Definitions.Def_MCAListDecoding_PowersGenerator_Curves

namespace MCAListDecoding.PowersGenerator

/-- Lemma 4.10 (a curve with a point outside it), p. 29, under the §4 standing hypotheses
(`γ = e / n`). If some seed of `B` does not lie on the curve `P`, then `s_P ≥ Δ_C - γ n`,
equivalently `z_P ≤ 1 - δ_C + γ`. -/
theorem lemma_4_10 {F Alph : Type*} [Field F] [Fintype F] [AddCommGroup Alph] [Module F Alph]
    [FiniteDimensional F Alph] {n : ℕ} (C : Submodule F (Fin n → Alph)) (hC : C ≠ ⊥)
    (d : ℕ) (hd : 1 ≤ d) (S : Finset F) (hS : S.Nonempty) (u : Fin (d + 1) → Fin n → Alph)
    (e : ℕ) (he : 1 ≤ e) (hΔ : 2 * e < minDist C)
    (hJ : (e : ℝ) / n < johnsonRadius (d + 2) (relDist C))
    (P : Curve C d)
    (hout : ∃ y ∈ badSeeds C d ((e : ℝ) / n) u S, decoded C d e u y ≠ curveEval P y) :
    (minDist C : ℤ) - (e : ℤ) ≤ (curveS u P : ℤ) ∧
      curveZ u P ≤ 1 - relDist C + (e : ℝ) / n := by sorry

end MCAListDecoding.PowersGenerator
