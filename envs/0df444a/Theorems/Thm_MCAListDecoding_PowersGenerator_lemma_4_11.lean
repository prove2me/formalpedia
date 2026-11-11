-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_4_11
-- name    : MCAListDecoding.PowersGenerator.lemma_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:45.872287+00:00
-- url     : https://prove2.me/theorems/409f9b8c-0ad9-4c75-879c-3f0682851eb5
-- title:
--   Lemma 4.11 — Corrádi-type bound on curves with z_P > τ; at most 4 for τ = (1−γ+√(1−δ_C))/2
-- statement:
--   Throughout §4 (p. 27) the standing hypotheses are $\gamma n \ge 1$, $2\gamma n < \Delta_C$ and $\gamma < J_{d+2}(\delta_C)$, with $\gamma n = e$ an integer. Let $\tau\in(\sqrt{1-\delta_C},1)$. The number of curves $P$ with $z_P>\tau$ is at most
--   $$\frac{\tau-(1-\delta_C)}{\tau^2-(1-\delta_C)}.$$
--   In particular, if $\tau=\frac{1-\gamma+\sqrt{1-\delta_C}}2$ there are at most $4$ such curves.
--
--   Differences from the source:
--   - encoding: radius γ ∈ [0,1] with γn an integer (convention (2), p. 27) → a natural number e (= γn) and the real radius e/n; e ≤ n is implied by 2e < Δ_C ≤ n; reason: the paper's integer-radius convention (2); every γ with γn ∈ {0,…,n} is e/n for e = γn
--   - encoding: a code C with minimum distance Δ_C (defined for codes with at least two codewords) → hypothesis C ≠ ⊥, with minDist C the minimum weight of a nonzero codeword; reason: Δ_C and δ_C are undefined for the zero code; the hypothesis only excludes that undefined case
--   - encoding: Σ, [n] = {1,…,n}, words u_0,…,u_d → Alph, Fin n (0-based coordinates), u : Fin (d+1) → Fin n → Alph; reason: Lean naming and indexing conventions; no instance changes
--   - encoding: the number of curves P with z_P > τ is at most … → every Finset of curves with z_P > τ has cardinality at most …; reason: the set of curves is finite (F finite, Σ finite-dimensional); bounding every finite subfamily is the same statement and avoids a junk cardinality
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma 4.11, pp. 29–30

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code
import Definitions.Def_MCAListDecoding_PowersGenerator_Curves

namespace MCAListDecoding.PowersGenerator

/-- Lemma 4.11 (few large curves, Corrádi-type bound), pp. 29–30, under the §4 standing hypotheses
(`γ = e / n`). For `τ ∈ (√(1 - δ_C), 1)`, the number of curves `P` with `z_P > τ` is at most
`(τ - (1 - δ_C))/(τ² - (1 - δ_C))`; in particular, for `τ = (1 - γ + √(1 - δ_C))/2` there are at
most `4` such curves. "The number of curves" is expressed as: every finite set of such curves
has at most that many elements. -/
theorem lemma_4_11 {F Alph : Type*} [Field F] [Fintype F] [AddCommGroup Alph] [Module F Alph]
    [FiniteDimensional F Alph] {n : ℕ} (C : Submodule F (Fin n → Alph)) (hC : C ≠ ⊥)
    (d : ℕ) (hd : 1 ≤ d) (S : Finset F) (hS : S.Nonempty) (u : Fin (d + 1) → Fin n → Alph)
    (e : ℕ) (he : 1 ≤ e) (hΔ : 2 * e < minDist C)
    (hJ : (e : ℝ) / n < johnsonRadius (d + 2) (relDist C)) :
    (∀ τ : ℝ, Real.sqrt (1 - relDist C) < τ → τ < 1 →
      ∀ Ps : Finset (Curve C d), (∀ P ∈ Ps, τ < curveZ u P) →
        (Ps.card : ℝ) ≤ (τ - (1 - relDist C)) / (τ ^ 2 - (1 - relDist C))) ∧
    (∀ Ps : Finset (Curve C d),
      (∀ P ∈ Ps, (1 - (e : ℝ) / n + Real.sqrt (1 - relDist C)) / 2 < curveZ u P) →
        Ps.card ≤ 4) := by sorry

end MCAListDecoding.PowersGenerator
