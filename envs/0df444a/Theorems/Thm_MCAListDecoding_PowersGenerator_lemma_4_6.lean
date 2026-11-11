-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_4_6
-- name    : MCAListDecoding.PowersGenerator.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:45.45652+00:00
-- url     : https://prove2.me/theorems/e1ab6161-3a5b-40c3-83a8-f2256482a86f
-- title:
--   Lemma 4.6 — interpolation through d+1 decoded points; common agreement set is T_P
-- statement:
--   Throughout §4 (p. 27) the standing hypotheses are $\gamma n \ge 1$, $2\gamma n < \Delta_C$ and $\gamma < J_{d+2}(\delta_C)$, with $\gamma n = e$ an integer. Let $x_1,\dots,x_\ell\in B$ be distinct, $\ell=d+1$. There is a unique curve $P$ with $P(x_m)=c_{x_m}$ for all $m\in[\ell]$, and
--   $$A(x_1)\cap\cdots\cap A(x_\ell)=T_P.$$
--
--   Differences from the source:
--   - encoding: radius γ ∈ [0,1] with γn an integer (convention (2), p. 27) → a natural number e (= γn) and the real radius e/n; e ≤ n is implied by 2e < Δ_C ≤ n; reason: the paper's integer-radius convention (2); every γ with γn ∈ {0,…,n} is e/n for e = γn
--   - encoding: a code C with minimum distance Δ_C (defined for codes with at least two codewords) → hypothesis C ≠ ⊥, with minDist C the minimum weight of a nonzero codeword; reason: Δ_C and δ_C are undefined for the zero code; the hypothesis only excludes that undefined case
--   - encoding: the unique codeword c_x within distance γn of u(x) (Lemma 4.2) → decoded C d e u x, a codeword within Hamming distance e of combinedWord d u x chosen by Classical.choose (0 if none); reason: under 2e < Δ_C the codeword is unique on bad seeds (Lemma 4.2), so it is the paper's c_x there
--   - encoding: Σ, [n] = {1,…,n}, words u_0,…,u_d → Alph, Fin n (0-based coordinates), u : Fin (d+1) → Fin n → Alph; reason: Lean naming and indexing conventions; no instance changes
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma 4.6, p. 28

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code
import Definitions.Def_MCAListDecoding_PowersGenerator_Curves

namespace MCAListDecoding.PowersGenerator

/-- Lemma 4.6 (interpolation), p. 28, under the §4 standing hypotheses (`γ = e / n`). For
`ℓ = d + 1` distinct bad seeds `x_1, …, x_ℓ` there is a unique curve `P` with
`P(x_m) = c_{x_m}` for all `m`, and `A(x_1) ∩ ⋯ ∩ A(x_ℓ) = T_P`. -/
theorem lemma_4_6 {F Alph : Type*} [Field F] [Fintype F] [AddCommGroup Alph] [Module F Alph]
    [FiniteDimensional F Alph] {n : ℕ} (C : Submodule F (Fin n → Alph)) (hC : C ≠ ⊥)
    (d : ℕ) (hd : 1 ≤ d) (S : Finset F) (hS : S.Nonempty) (u : Fin (d + 1) → Fin n → Alph)
    (e : ℕ) (he : 1 ≤ e) (hΔ : 2 * e < minDist C)
    (hJ : (e : ℝ) / n < johnsonRadius (d + 2) (relDist C))
    (xs : Fin (d + 1) → F) (hinj : Function.Injective xs)
    (hbad : ∀ m, xs m ∈ badSeeds C d ((e : ℝ) / n) u S) :
    ∃ P : Curve C d, (∀ m, curveEval P (xs m) = decoded C d e u (xs m)) ∧
      (∀ Q : Curve C d, (∀ m, curveEval Q (xs m) = decoded C d e u (xs m)) → Q = P) ∧
      commonAgreement C d e u xs = curveDomain u P := by sorry

end MCAListDecoding.PowersGenerator
