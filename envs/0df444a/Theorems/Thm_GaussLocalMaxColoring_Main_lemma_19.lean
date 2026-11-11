-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_19
-- name    : GaussLocalMaxColoring.Main.lemma_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:22:15.525728+00:00
-- url     : https://prove2.me/theorems/c6910240-45c3-48bf-ae42-6e44b5a741cf
-- title:
--   Lemma 19 — a failed level deletes fewer than $2T/\delta$ vertices; over $\ell$ failed levels fewer than $2\ell T/\delta$
-- statement:
--   Consider one trial of Algorithm 2 on a graph $G$ with vectors $\{v_x\}$, threshold $\delta>0$, target $T$ and $R\ge1$ samples per level, as a function of its Gaussian samples. If every independent set $I^{(i)}$ sampled at level $j$ ($1\le j\le\ell$) has size less than $T$, then $|F_{j-1}\setminus F_j|<2T/\delta$. In particular, if this holds at all levels $j=1,\dots,\ell$, then $\sum_{j=1}^{\ell}|F_{j-1}\setminus F_j|<2\ell T/\delta$.
--
--   **Formalization Note.** The second claim is false as printed when $\ell=\lceil\log n\rceil=0$ ($n\le1$): both sides are $0$ (insight I4). It is stated as printed.
--
--   Differences from the source:
--   - generalization: §4, high-degree parameters of Table 2, a strict vector 3-coloring ("Lemma 19 holds for arbitrary δ and T") → any graph, any vectors, any real δ > 0, any T ∈ ℕ; reason: the proof is pure counting; the paper's settings (Table 2, Table 3, Appendix A) are instances
--   - encoding: R ∈ ℕ samples per level, p̂_j(x) = R⁻¹ Σ_i 1[x ∈ I^{(i)}] → 1 ≤ R; reason: p̂_j is undefined for R = 0
--   - encoding: the trial stops at its first SUCCESS; F_j exists only if levels 1..j failed → cores computed for every level as if no level succeeded (they equal the trial's cores whenever constructed); the hypothesis is on the sets sampled at level j; reason: a total function of the samples; the statement is about levels whose sampled sets all have size < T
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 19, printed p. 18 (PDF 20)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Iterative

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 19** (p. 18, PDF 20), for one trial of Algorithm 2 with any graph, any vectors, any
`δ > 0`, any `T` and `R ≥ 1` samples per level: if every sampled independent set at level `j`
has size `< T`, then `|F_{j−1} ∖ F_j| < 2T/δ`; if this holds at all levels `j = 1, …, ℓ`, then
`Σ_{j=1}^{ℓ} |F_{j−1} ∖ F_j| < 2ℓT/δ`. -/
theorem lemma_19 {n d R : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ)
    (hδ : 0 < δ) (T : ℕ) (hR : 1 ≤ R) (ω : Fin (numLevels n) × Fin R → Space d) :
    (∀ j, 1 ≤ j → j ≤ numLevels n → (∀ i, (sampleSet G v δ ω j i).card < T) →
      ((cores G v δ ω (j - 1) \ cores G v δ ω j).card : ℝ) < 2 * T / δ) ∧
    ((∀ j, 1 ≤ j → j ≤ numLevels n → ∀ i, (sampleSet G v δ ω j i).card < T) →
      (∑ j ∈ Finset.Icc 1 (numLevels n),
          ((cores G v δ ω (j - 1) \ cores G v δ ω j).card : ℝ)) <
        2 * (numLevels n : ℝ) * T / δ) := by sorry

end GaussLocalMaxColoring.Main
