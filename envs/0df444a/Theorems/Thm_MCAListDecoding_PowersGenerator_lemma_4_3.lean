-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_4_3
-- name    : MCAListDecoding.PowersGenerator.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:00.683005+00:00
-- url     : https://prove2.me/theorems/5651ec21-6f1d-4f2f-a78f-7e3cc0bc5061
-- title:
--   Lemma 4.3 — at radius zero there are at most d bad seeds
-- statement:
--   In the setting of §4 ($F$ finite, $\Sigma$ finite-dimensional, $C\subseteq\Sigma^n$ a nonzero $F$-linear code, $d\ge1$, $S\subseteq F$ nonempty, words $u_0,\dots,u_d$): if $\gamma=0$ then $|B|\le d$.
--
--   Differences from the source:
--   - encoding: a code C with minimum distance Δ_C (defined for codes with at least two codewords) → hypothesis C ≠ ⊥, with minDist C the minimum weight of a nonzero codeword; reason: Δ_C and δ_C are undefined for the zero code; the hypothesis only excludes that undefined case
--   - encoding: Σ, [n] = {1,…,n}, words u_0,…,u_d → Alph, Fin n (0-based coordinates), u : Fin (d+1) → Fin n → Alph; reason: Lean naming and indexing conventions; no instance changes
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma 4.3, p. 27

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code

namespace MCAListDecoding.PowersGenerator

/-- Lemma 4.3 (the case `γ = 0`), p. 27: at radius `0` there are at most `d` MCA-bad seeds. -/
theorem lemma_4_3 {F Alph : Type*} [Field F] [Fintype F] [AddCommGroup Alph] [Module F Alph]
    [FiniteDimensional F Alph] {n : ℕ} (C : Submodule F (Fin n → Alph)) (hC : C ≠ ⊥)
    (d : ℕ) (hd : 1 ≤ d) (S : Finset F) (hS : S.Nonempty) (u : Fin (d + 1) → Fin n → Alph) :
    (badSeeds C d 0 u S).card ≤ d := by sorry

end MCAListDecoding.PowersGenerator
