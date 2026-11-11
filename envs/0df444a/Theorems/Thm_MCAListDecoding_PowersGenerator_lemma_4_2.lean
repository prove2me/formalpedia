-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_4_2
-- name    : MCAListDecoding.PowersGenerator.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:45.541033+00:00
-- url     : https://prove2.me/theorems/498d0afa-3101-45d5-8770-56565caf3d78
-- title:
--   Lemma 4.2 — decoding: unique close codeword, full agreement set is a badness witness
-- statement:
--   Let $F$ be a finite field, $\Sigma$ a finite-dimensional $F$-vector space, $C\subseteq\Sigma^n$ a nonzero $F$-linear code, $d\ge1$, $S\subseteq F$ nonempty, $u_0,\dots,u_d\in\Sigma^n$, and $e=\gamma n$ an integer radius. Assume $2e<\Delta_C$. For every MCA-bad seed $x\in B$ there is a unique codeword $c_x\in C$ with $\Delta(u(x),c_x)\le e$. Moreover the full agreement set $A(x)=\{i : u_i(x)=c_x[i]\}$ is itself a badness witness: $|A(x)|\ge n(1-\gamma)$, $u(x)|_{A(x)}\in C|_{A(x)}$, and $u_j|_{A(x)}\notin C|_{A(x)}$ for some $j$.
--
--   Differences from the source:
--   - encoding: radius γ ∈ [0,1] with γn an integer (convention (2), p. 27) → a natural number e (= γn) and the real radius e/n; e ≤ n is implied by 2e < Δ_C ≤ n; reason: the paper's integer-radius convention (2); every γ with γn ∈ {0,…,n} is e/n for e = γn
--   - encoding: a code C with minimum distance Δ_C (defined for codes with at least two codewords) → hypothesis C ≠ ⊥, with minDist C the minimum weight of a nonzero codeword; reason: Δ_C and δ_C are undefined for the zero code; the hypothesis only excludes that undefined case
--   - encoding: the unique codeword c_x within distance γn of u(x) (Lemma 4.2) → decoded C d e u x, a codeword within Hamming distance e of combinedWord d u x chosen by Classical.choose (0 if none); reason: under 2e < Δ_C the codeword is unique on bad seeds (Lemma 4.2), so it is the paper's c_x there
--   - encoding: Σ, [n] = {1,…,n}, words u_0,…,u_d → Alph, Fin n (0-based coordinates), u : Fin (d+1) → Fin n → Alph; reason: Lean naming and indexing conventions; no instance changes
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma 4.2, p. 27

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code
import Definitions.Def_MCAListDecoding_PowersGenerator_Curves

namespace MCAListDecoding.PowersGenerator

/-- Lemma 4.2 (decoding and full agreement sets), p. 27. Integer radius `e = γ n` (convention (2)),
so the bad seeds are those for the real radius `e / n`. If `2 e < Δ_C`, every bad seed `x` has a
unique codeword `c_x ∈ C` with `Δ(u(x), c_x) ≤ e`; and the full agreement set
`A(x) = {i : u_i(x) = c_x[i]}` is itself a badness witness. -/
theorem lemma_4_2 {F Alph : Type*} [Field F] [Fintype F] [AddCommGroup Alph] [Module F Alph]
    [FiniteDimensional F Alph] {n : ℕ} (C : Submodule F (Fin n → Alph)) (hC : C ≠ ⊥)
    (d : ℕ) (hd : 1 ≤ d) (S : Finset F) (hS : S.Nonempty) (u : Fin (d + 1) → Fin n → Alph)
    (e : ℕ) (hΔ : 2 * e < minDist C)
    (x : F) (hx : x ∈ badSeeds C d ((e : ℝ) / n) u S) :
    (∃! c : Fin n → Alph, c ∈ C ∧ hamDist (combinedWord d u x) c ≤ e) ∧
      ((n : ℝ) * (1 - (e : ℝ) / n) ≤ ((agreementSet C d e u x).card : ℝ) ∧
        RestrictMem C (agreementSet C d e u x) (combinedWord d u x) ∧
        ∃ j : Fin (d + 1), ¬ RestrictMem C (agreementSet C d e u x) (u j)) := by sorry

end MCAListDecoding.PowersGenerator
