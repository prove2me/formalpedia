-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_37
-- name    : GaussLocalMaxColoring.Main.lemma_37
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:23:37.361441+00:00
-- url     : https://prove2.me/theorems/d34ce85e-b971-4acf-866b-b2cd44c1bc97
-- title:
--   Lemma 37 — a band whose rounding fails has $|S|\le\exp((C_D(\rho)+\eta)t^2/2)$
-- statement:
--   Section 5 setting, with the rounding slack $\varepsilon_{\rm thr}$ and the grid step $h$ ($1/h\in\mathbb N$) sufficiently small and $n$ sufficiently large (depending on the $o(1)$ family $g$ of VectorColoring's guarantee): for every output of BuildVector satisfying Lemma 34 and every band $S=S_{r,P}$, if the band rounding returns FAIL (its set has size $<T$) and its internal call to VectorColoring meets its guarantee, then for every $\rho\in P$,
--   $$|S|\le\exp\Big((C_D(\rho)+\eta)\frac{t^2}2\Big).$$
--
--   Differences from the source:
--   - generalization: the band witnesses produced by BuildVector → any vectors and witnesses satisfying Lemma 34 (BVGuarantee), any band partition; reason: the proof uses only these guarantees
--   - reading: ε_thr and h "fixed constants … sufficiently small depending only on β and η" (pp. 33–34) → ∃ ε₀, h₀ > 0 such that the statement holds for every ε_thr ≤ min(ε₀, 1/30) and h ≤ min(h₀, 1/8) with 1/h ∈ ℕ; reason: any sufficiently small choice satisfies the requirement of p. 34
--   - reading: no threshold on n is printed; the hypothesis "the call meets its guarantee" carries Theorem 2's o(1) term → ∃ N₀ (chosen after ε_thr, h and the o(1) family g) such that the conclusion holds for every n ≥ N₀; reason: the guarantee is asymptotic: at a fixed n an o(1) family can make it say only that I′ is nonempty, and the proof argues "for sufficiently large n" throughout
--   - reading: "Suppose that the band-rounding procedure returns FAIL and that … that call meets its guarantee" → for VectorColoring's returned set I′: VCMeets … I′ and |bandOut … I′| < T; reason: the procedure's output is determined by I′
--   - encoding: §5 standing assumptions (G 3-colorable, every degree ≤ n^β, β = 0.692601; Table 3 parameters as functions of n) → binders G.Colorable 3, maxDegOn G univ ≤ n^beta5, and the Table 3 definitions of the Section5 module; reason: the section states them once (pp. 31, 35); they are hypotheses of every §5 lemma
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
--   - encoding: vectors in R^d, g ∼ N(0, I_d), P_g → Space d = EuclideanSpace ℝ (Fin d), any d, Mathlib stdGaussian (gaussProb); reason: Lean convention; same instances
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 37, printed p. 38 (PDF 40)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Bands

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 37** (Band bound after failed rounding; p. 38, PDF 40). Section 5 setting, with the
rounding slack `ε_thr` and the grid step `h` sufficiently small (depending only on `β`, `η`) and
`n` sufficiently large (depending on the `o(1)` family `g` of VectorColoring's guarantee): for
every band `S = S_{r,P}`, if the band rounding returns `FAIL` (its set has size `< T`) and its
internal call to VectorColoring meets its guarantee, then `|S| ≤ exp((C_D(ρ) + η) t²/2)` for
every `ρ ∈ P`. -/
theorem lemma_37 :
    ∃ ε₀ h₀ : ℝ, 0 < ε₀ ∧ 0 < h₀ ∧
      ∀ εthr h : ℝ, 0 < εthr → εthr ≤ ε₀ → εthr ≤ 1 / 30 → 0 < h → h ≤ h₀ → h ≤ 1 / 8 →
      (∃ N : ℕ, h * N = 1) →
      ∀ g : ℝ → ℝ → ℕ → ℝ, (∀ k b, IsLittleO1 (g k b)) →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ (d d' : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
        (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ beta5 →
        ∀ (Pt : Finset Ival), IsBandPartition n Pt →
        ∀ (v : Fin n → Space d) (W : Fin n → Ival → WIdx n → Space d'), BVGuarantee G Pt v W →
        ∀ (r : Fin n) (P : Ival), P ∈ Pt →
        ∀ I' : Finset (Fin n),
          VCMeets g h (vcK P εthr) G (vcInput G (gram v) r P (gram (W r P)) εthr) I' →
          (bandOut G (gram v) r P (gram (W r P)) εthr I').card < target5 n →
          ∀ ρ ∈ P.toSet,
            ((band (gram v) r P).card : ℝ) ≤ Real.exp ((capacity D5 ρ + eta5) * t5 n ^ 2 / 2) := by sorry

end GaussLocalMaxColoring.Main
