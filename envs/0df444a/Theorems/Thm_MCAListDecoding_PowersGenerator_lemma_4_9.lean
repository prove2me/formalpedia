-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_4_9
-- name    : MCAListDecoding.PowersGenerator.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:54.283372+00:00
-- url     : https://prove2.me/theorems/abd9801c-6035-4900-8e8a-76c1b05f5484
-- title:
--   Lemma 4.9 — noncoherent tuples have common agreement at most n − Δ_C
-- statement:
--   Throughout §4 (p. 27) the standing hypotheses are $\gamma n \ge 1$, $2\gamma n < \Delta_C$ and $\gamma < J_{d+2}(\delta_C)$, with $\gamma n = e$ an integer. The common agreement set $A(x_1)\cap\cdots\cap A(x_h)$ of a noncoherent tuple of $h=d+2$ distinct seeds of $B$ has size at most $n-\Delta_C$.
--
--   Differences from the source:
--   - encoding: radius γ ∈ [0,1] with γn an integer (convention (2), p. 27) → a natural number e (= γn) and the real radius e/n; e ≤ n is implied by 2e < Δ_C ≤ n; reason: the paper's integer-radius convention (2); every γ with γn ∈ {0,…,n} is e/n for e = γn
--   - encoding: a code C with minimum distance Δ_C (defined for codes with at least two codewords) → hypothesis C ≠ ⊥, with minDist C the minimum weight of a nonzero codeword; reason: Δ_C and δ_C are undefined for the zero code; the hypothesis only excludes that undefined case
--   - encoding: the unique codeword c_x within distance γn of u(x) (Lemma 4.2) → decoded C d e u x, a codeword within Hamming distance e of combinedWord d u x chosen by Classical.choose (0 if none); reason: under 2e < Δ_C the codeword is unique on bad seeds (Lemma 4.2), so it is the paper's c_x there
--   - encoding: Σ, [n] = {1,…,n}, words u_0,…,u_d → Alph, Fin n (0-based coordinates), u : Fin (d+1) → Fin n → Alph; reason: Lean naming and indexing conventions; no instance changes
--   - encoding: |common agreement set| ≤ n − Δ_C → the inequality cast to ℤ; reason: avoids truncated natural subtraction; same inequality since Δ_C ≤ n
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma 4.9, p. 29

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code
import Definitions.Def_MCAListDecoding_PowersGenerator_Curves

namespace MCAListDecoding.PowersGenerator

/-- Lemma 4.9 (noncoherent tuples), p. 29, under the §4 standing hypotheses (`γ = e / n`). The
common agreement set of a noncoherent tuple of `h = d + 2` distinct bad seeds has size at most
`n - Δ_C`. -/
theorem lemma_4_9 {F Alph : Type*} [Field F] [Fintype F] [AddCommGroup Alph] [Module F Alph]
    [FiniteDimensional F Alph] {n : ℕ} (C : Submodule F (Fin n → Alph)) (hC : C ≠ ⊥)
    (d : ℕ) (hd : 1 ≤ d) (S : Finset F) (hS : S.Nonempty) (u : Fin (d + 1) → Fin n → Alph)
    (e : ℕ) (he : 1 ≤ e) (hΔ : 2 * e < minDist C)
    (hJ : (e : ℝ) / n < johnsonRadius (d + 2) (relDist C))
    (xs : Fin (d + 2) → F) (hinj : Function.Injective xs)
    (hbad : ∀ m, xs m ∈ badSeeds C d ((e : ℝ) / n) u S)
    (hnc : ¬ IsCoherent C d e u xs) :
    ((commonAgreement C d e u xs).card : ℤ) ≤ (n : ℤ) - (minDist C : ℤ) := by sorry

end MCAListDecoding.PowersGenerator
