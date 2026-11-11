-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_4_5
-- name    : MCAListDecoding.PowersGenerator.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:52.00327+00:00
-- url     : https://prove2.me/theorems/2428f976-dae4-4f8b-abfb-feab12a0fe8a
-- title:
--   Lemma 4.5 — root counting on a curve
-- statement:
--   Throughout §4 (p. 27) the standing hypotheses are $\gamma n \ge 1$, $2\gamma n < \Delta_C$ and $\gamma < J_{d+2}(\delta_C)$, with $\gamma n = e$ an integer. Let $P$ be a curve and $B'\subseteq B$. Then
--   $$|\{x\in B' : c_x=P(x)\}|\le d(\gamma n+1).$$
--   If moreover $z_P<1-\gamma$, then
--   $$|\{x\in B' : c_x=P(x)\}|\le d\,\frac{1-z_P}{1-\gamma-z_P}=d+\frac{d\gamma}{1-\gamma-z_P}.$$
--
--   Differences from the source:
--   - encoding: radius γ ∈ [0,1] with γn an integer (convention (2), p. 27) → a natural number e (= γn) and the real radius e/n; e ≤ n is implied by 2e < Δ_C ≤ n; reason: the paper's integer-radius convention (2); every γ with γn ∈ {0,…,n} is e/n for e = γn
--   - encoding: a code C with minimum distance Δ_C (defined for codes with at least two codewords) → hypothesis C ≠ ⊥, with minDist C the minimum weight of a nonzero codeword; reason: Δ_C and δ_C are undefined for the zero code; the hypothesis only excludes that undefined case
--   - encoding: the unique codeword c_x within distance γn of u(x) (Lemma 4.2) → decoded C d e u x, a codeword within Hamming distance e of combinedWord d u x chosen by Classical.choose (0 if none); reason: under 2e < Δ_C the codeword is unique on bad seeds (Lemma 4.2), so it is the paper's c_x there
--   - encoding: Σ, [n] = {1,…,n}, words u_0,…,u_d → Alph, Fin n (0-based coordinates), u : Fin (d+1) → Fin n → Alph; reason: Lean naming and indexing conventions; no instance changes
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma 4.5, p. 28

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code
import Definitions.Def_MCAListDecoding_PowersGenerator_Curves

namespace MCAListDecoding.PowersGenerator

open Classical in
/-- Lemma 4.5 (root counting on a curve), p. 28, under the §4 standing hypotheses
`γ n ≥ 1`, `2 γ n < Δ_C`, `γ < J_{d+2}(δ_C)` with `γ = e / n`. For a curve `P` and `B' ⊆ B`, the
number of seeds of `B'` lying on `P` is at most `d (γ n + 1)`; if moreover `z_P < 1 - γ`, it is
at most `d (1 - z_P)/(1 - γ - z_P) = d + d γ/(1 - γ - z_P)`. -/
theorem lemma_4_5 {F Alph : Type*} [Field F] [Fintype F] [AddCommGroup Alph] [Module F Alph]
    [FiniteDimensional F Alph] {n : ℕ} (C : Submodule F (Fin n → Alph)) (hC : C ≠ ⊥)
    (d : ℕ) (hd : 1 ≤ d) (S : Finset F) (hS : S.Nonempty) (u : Fin (d + 1) → Fin n → Alph)
    (e : ℕ) (he : 1 ≤ e) (hΔ : 2 * e < minDist C)
    (hJ : (e : ℝ) / n < johnsonRadius (d + 2) (relDist C))
    (P : Curve C d) (B' : Finset F) (hB' : B' ⊆ badSeeds C d ((e : ℝ) / n) u S) :
    (((B'.filter fun x => decoded C d e u x = curveEval P x).card : ℝ) ≤ d * ((e : ℝ) + 1)) ∧
      (curveZ u P < 1 - (e : ℝ) / n →
        ((B'.filter fun x => decoded C d e u x = curveEval P x).card : ℝ) ≤
            d * (1 - curveZ u P) / (1 - (e : ℝ) / n - curveZ u P) ∧
          d * (1 - curveZ u P) / (1 - (e : ℝ) / n - curveZ u P) =
            d + d * ((e : ℝ) / n) / (1 - (e : ℝ) / n - curveZ u P)) := by sorry

end MCAListDecoding.PowersGenerator
