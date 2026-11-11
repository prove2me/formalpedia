-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_46
-- name    : GaussLocalMaxColoring.Main.lemma_46
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:23:35.927304+00:00
-- url     : https://prove2.me/theorems/01f1a4b1-b6db-4bad-8f11-568f14d3c4b5
-- title:
--   Lemma 46 — one SparseProgress trial succeeds with probability $\ge1/2$; $\Theta(\log n)$ trials with probability $\ge1-n^{-C}$
-- statement:
--   Section 5 setting with $\varepsilon_{\rm thr}$ and $h$ sufficiently small, for every constant $K_{\mathcal P}$ and $o(1)$ family $g$ of VectorColoring's guarantee, and $n$ sufficiently large. Let $G$ be 3-colorable on $n$ vertices with $\Delta(G)\le n^\beta$, $\mathcal P$ a band partition with $|\mathcal P|\le K_{\mathcal P}\log n+K_{\mathcal P}$, $(\{v_i\},\mathcal S)$ an output of BuildVector satisfying Lemma 34, the bands processed in any order, and VectorColoring any randomized subroutine (on any probability space) that always returns an independent subset of its input and, in each band rounding, meets its guarantee with probability at least $1-n^{-3}$. Then one trial of SparseProgress, which makes $\ell R\le Kn^K+K$ calls of Algorithm 1 and $n|\mathcal P|$ band roundings, returns an independent set $I$ with $|I|\ge T$ with probability at least $1/2$; and for every $C>0$ there is $c>0$ such that $\lceil c\log n\rceil$ independent trials return such a set with probability at least $1-n^{-C}$.
--
--   Differences from the source:
--   - generalization: BuildVector's output → any vectors and witnesses satisfying Lemma 34 (BVGuarantee); reason: the proof uses only these guarantees
--   - generalization: VectorColoring = Theorem 2's algorithm amplified by Θ(log n) repetitions (§5.6), failure probability ≤ n^{−3} per call → any randomized subroutine on any probability space (Ω, μ) that always returns an independent subset of its input and meets its guarantee (VCMeets, o(1) family g) in each band rounding with probability ≥ 1 − n^{−3}; reason: this is exactly what the proof uses of the amplified calls; the paper's VectorColoring is an instance by Theorem 2
--   - generalization: the fixed partition 𝒫 and the order in which Algorithm 3 iterates over 𝒮 → every band partition with |𝒫| ≤ K_𝒫 log n + K_𝒫 and every order of the bands; reason: covers the paper's choices
--   - reading: "one trial … runs in polynomial time"; "a polynomial-time algorithm" → one trial makes ℓR ≤ K·n^K + K calls of Algorithm 1 (and n|𝒫| band roundings, each one call of VectorColoring, polynomial by Theorem 2, after BuildVector, polynomial by Lemma 34); probabilities under μ ⊗ (product Gaussian law), trials independent; reason: analysis layer (finding I1)
--   - reading: ε_thr, h sufficiently small; "for sufficiently large n"; Θ(log n) trials → ∃ ε₀, h₀ (every smaller ε_thr, h with 1/h ∈ ℕ); ∃ N₀ after ε_thr, h, K_𝒫, g; ⌈c log n⌉ trials with c chosen after C, before n; reason: the paper's uniform asymptotic convention
--   - encoding: §5 standing assumptions (G 3-colorable, every degree ≤ n^β, β = 0.692601; Table 3 parameters as functions of n) → binders G.Colorable 3, maxDegOn G univ ≤ n^beta5, and the Table 3 definitions of the Section5 module; reason: the section states them once (pp. 31, 35); they are hypotheses of every §5 lemma
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
--   - encoding: vectors in R^d, g ∼ N(0, I_d), P_g → Space d = EuclideanSpace ℝ (Fin d), any d, Mathlib stdGaussian (gaussProb); reason: Lean convention; same instances
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 46, printed p. 51 (PDF 53); proof pp. 51–52 (PDF 53–54)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Bands

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 46** (pp. 51–52, PDF 53–54). Section 5 setting, `ε_thr` and `h` sufficiently small,
`|𝒫| ≤ K_𝒫 log n + K_𝒫`, any band order, and `n` sufficiently large. Let `G` be 3-colorable on
`n` vertices with `Δ(G) ≤ n^β`, `({v_i}, 𝒮)` an output of BuildVector with the guarantees of
Lemma 34, and VectorColoring (amplified) any randomized subroutine that always returns an
independent subset of its input and, in each band rounding, meets its guarantee with probability
at least `1 − n^{−3}`. Then one trial of SparseProgress (`ℓR` calls of Algorithm 1, a polynomial
number) returns an independent set `I` with `|I| ≥ T` with probability at least `1/2`; and for
every `C > 0` there is `c > 0` such that `⌈c log n⌉` independent trials return such a set with
probability at least `1 − n^{−C}`. -/
theorem lemma_46 :
    ∃ ε₀ h₀ : ℝ, 0 < ε₀ ∧ 0 < h₀ ∧
      ∀ εthr h : ℝ, 0 < εthr → εthr ≤ ε₀ → εthr ≤ 1 / 30 → 0 < h → h ≤ h₀ → h ≤ 1 / 8 →
      (∃ N : ℕ, h * N = 1) →
      ∀ KP : ℝ, ∀ g : ℝ → ℝ → ℕ → ℝ, (∀ k b, IsLittleO1 (g k b)) →
      (∃ K : ℝ, ∀ n : ℕ, ((numLevels n * runs5 n : ℕ) : ℝ) ≤ K * (n : ℝ) ^ K + K) ∧
      ∃ N₀ : ℕ,
        (∀ n : ℕ, N₀ ≤ n →
          ∀ (d d' : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
          (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ beta5 →
          ∀ Pt : Finset Ival, IsBandPartition n Pt → (Pt.card : ℝ) ≤ KP * Real.log n + KP →
          ∀ (v : Fin n → Space d) (W : Fin n → Ival → WIdx n → Space d'), BVGuarantee G Pt v W →
          ∀ L : List (Fin n × Ival), L.Nodup → (∀ b, b ∈ L ↔ b.2 ∈ Pt) →
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (vc : Ω → Fin n → Ival → Finset (Fin n)),
          (∀ ω r P, P ∈ Pt →
            vc ω r P ⊆ vcInput G (gram v) r P (gram (W r P)) εthr ∧ IsIndep G (vc ω r P)) →
          (∀ r P, P ∈ Pt →
            μ.real {ω | VCMeets g h (vcK P εthr) G
                (vcInput G (gram v) r P (gram (W r P)) εthr) (vc ω r P)} ≥
              1 - (n : ℝ) ^ (-3 : ℝ)) →
          (μ.prod (trialLaw n d (runs5 n))).real
              {p | TrialGood G (sparseTrial G v W εthr L (vc p.1) p.2)} ≥ 1 / 2) ∧
        (∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧
          ∀ n : ℕ, N₀ ≤ n →
          ∀ (d d' : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
          (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ beta5 →
          ∀ Pt : Finset Ival, IsBandPartition n Pt → (Pt.card : ℝ) ≤ KP * Real.log n + KP →
          ∀ (v : Fin n → Space d) (W : Fin n → Ival → WIdx n → Space d'), BVGuarantee G Pt v W →
          ∀ L : List (Fin n × Ival), L.Nodup → (∀ b, b ∈ L ↔ b.2 ∈ Pt) →
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (vc : Ω → Fin n → Ival → Finset (Fin n)),
          (∀ ω r P, P ∈ Pt →
            vc ω r P ⊆ vcInput G (gram v) r P (gram (W r P)) εthr ∧ IsIndep G (vc ω r P)) →
          (∀ r P, P ∈ Pt →
            μ.real {ω | VCMeets g h (vcK P εthr) G
                (vcInput G (gram v) r P (gram (W r P)) εthr) (vc ω r P)} ≥
              1 - (n : ℝ) ^ (-3 : ℝ)) →
          (Measure.pi fun _ : Fin ⌈c * Real.log n⌉₊ => μ.prod (trialLaw n d (runs5 n))).real
              {p | ∃ s, TrialGood G (sparseTrial G v W εthr L (vc (p s).1) (p s).2)} ≥
            1 - (n : ℝ) ^ (-C)) := by sorry

end GaussLocalMaxColoring.Main
