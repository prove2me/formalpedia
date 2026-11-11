-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_35
-- name    : GaussLocalMaxColoring.Main.lemma_35
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:23:27.971306+00:00
-- url     : https://prove2.me/theorems/21b7d4a3-495c-4a96-ad66-4bcb0b185691
-- title:
--   Lemma 35 — guarantee of band rounding
-- statement:
--   Section 5 setting: $G$ 3-colorable on $n$ vertices with maximum degree at most $n^\beta$ ($\beta=0.692601$), $\mathcal P$ a band partition, and $(\{v_i\},\mathcal S)$ an output of BuildVector satisfying Lemma 34. There is a constant $K$ such that for every $0<\varepsilon_{\rm thr}\le1/30$, every grid step $h\in(0,1/8]$ with $1/h\in\mathbb N$ and every $o(1)$ family $g$ of VectorColoring's guarantee, there is $g'\to0$ (an $o(1)$ as $|S|\to\infty$) such that for every band $S=S_{r,P}$:
--   $|S'|\ge\frac{\varepsilon_{\rm thr}}2|S|$;
--   (i) if $S$ is positive with $\rho_P\le\tfrac14$ and $\beta_+\in(0,1]$ satisfies $\Delta(G[S''])\le|S''|^{\beta_+}$, then whenever VectorColoring's returned set $I'$ meets its guarantee, RoundPositive's $I=I_0\cup I'$ is independent and $|I|\ge(\varepsilon_{\rm thr}|S|)^{\frac{2\tau(1+\beta_+)}{2\tau+\beta_+}-Kh-g'(|S|)}$;
--   (ii) if $S$ is positive with $\rho_P>\tfrac14$, then $G[S]$ is edgeless and $I_0=S'$ (hence $I=I_0=S'$);
--   (iii) if $S$ is negative and $\beta_-\in(0,1]$ satisfies $\Delta(G[S'])\le|S'|^{\beta_-}$, then whenever $I'$ meets its guarantee, RoundNegative's $I=I'$ is independent and $|I|\ge(\varepsilon_{\rm thr}|S|)^{\frac{2(1+\beta_-)(2\tau-1)}{(4+3\beta_-)\tau-(2+\beta_-)}-Kh-g'(|S|)}$.
--
--   **Formalization Note.** The first claim is stated as printed, for every $n$ and every $\varepsilon_{\rm thr}\in(0,1/30]$; its proof needs $e^{-3n}\le\varepsilon_{\rm thr}/2$ (insight I3).
--
--   Differences from the source:
--   - generalization: the band witnesses produced by BuildVector → any vectors and witness vectors satisfying every guarantee of Lemma 34 (BVGuarantee), any band partition; reason: the proof uses only Lemma 34's guarantees
--   - reading: "whenever the internal call to VectorColoring meets its guarantee" → a hypothesis on VectorColoring's returned set I′ (VCMeets): I′ ⊆ V(G′) independent with |I′| ≥ |V(G′)|^{1 − (k_h−2)β_h/(2+k_hβ_h) − g(|V(G′)|)}, for an o(1) family g (one function per grid pair (k_h, β_h)) quantified before the band; reason: VectorColoring's guarantee as stated on p. 37; the o(1) of Theorem 2 is not fixed by the paper
--   - reading: O(h) ("implied constant depends only on β") and o(1) → K·h with one constant K chosen first (β is fixed), and one function g′ → 0 of the band size |S|, chosen after ε_thr, h and g, before the graph and the band; reason: the paper's uniform asymptotic convention; the o(1) comes from Theorem 2's guarantee on G[S″] (resp. G[S′]), an o(1) in the size of the rounded graph, so it vanishes as |S| → ∞ (an o(1) in n is false for a small band of a large graph)
--   - reading: (ii) "G[S] is edgeless, and hence we have I = I₀ = S′" → Edgeless G S ∧ I₀ = S′ (then S″ = ∅ and I = I₀ ∪ I′ = S′ for any returned I′ ⊆ S″); reason: the printed consequence in terms of the defined sets
--   - encoding: witness vectors and ‖x_i‖², ‖x_{i,1}‖² + ‖x_{i,2}‖² → Gram matrix entries Y_(i,0),(i,0) and Y_(i,0),(i,0) + Y_(i,1),(i,1); reason: Gram encoding of the witnesses
--   - encoding: §5 standing assumptions (G 3-colorable, every degree ≤ n^β, β = 0.692601; Table 3 parameters as functions of n) → binders G.Colorable 3, maxDegOn G univ ≤ n^beta5, and the Table 3 definitions of the Section5 module; reason: the section states them once (pp. 31, 35); they are hypotheses of every §5 lemma
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
--   - encoding: vectors in R^d, g ∼ N(0, I_d), P_g → Space d = EuclideanSpace ℝ (Fin d), any d, Mathlib stdGaussian (gaussProb); reason: Lean convention; same instances
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 35, printed pp. 35–36 (PDF 37–38)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Bands

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 35** (Guarantee of band rounding; pp. 35–36, PDF 37–38). Section 5 setting: `G`
3-colorable on `n` vertices with maximum degree at most `n^β` (`β = 0.692601`), `𝒫` a band
partition, `({v_i}, 𝒮)` an output of BuildVector with the guarantees of Lemma 34. There is a
constant `K` (the `O(h)`) such that for every `0 < ε_thr ≤ 1/30`, every grid step `h ∈ (0, 1/8]`
with `1/h ∈ ℕ` and every `o(1)` family `g` of VectorColoring's guarantee there is `g′ → 0` (an `o(1)` as `|S| → ∞`) such
that for every band `S = S_{r,P}`:
`|S′| ≥ (ε_thr/2)|S|`;
(i) if `S` is positive with `ρ_P ≤ 1/4` and `β₊ ∈ (0, 1]` satisfies `Δ(G[S″]) ≤ |S″|^{β₊}`, then
whenever VectorColoring's returned set `I′` meets its guarantee, RoundPositive's set `I = I₀ ∪ I′`
is independent with `|I| ≥ (ε_thr|S|)^{2τ(1+β₊)/(2τ+β₊) − K h − g′(|S|)}`;
(ii) if `S` is positive with `ρ_P > 1/4`, then `G[S]` is edgeless and `I₀ = S′` (so `I = I₀ = S′`);
(iii) if `S` is negative and `β₋ ∈ (0, 1]` satisfies `Δ(G[S′]) ≤ |S′|^{β₋}`, then whenever `I′`
meets its guarantee, RoundNegative's set `I = I′` is independent with
`|I| ≥ (ε_thr|S|)^{2(1+β₋)(2τ−1)/((4+3β₋)τ−(2+β₋)) − K h − g′(|S|)}`. -/
theorem lemma_35 :
    ∃ K : ℝ, 0 < K ∧
      ∀ εthr h : ℝ, 0 < εthr → εthr ≤ 1 / 30 → 0 < h → h ≤ 1 / 8 → (∃ N : ℕ, h * N = 1) →
      ∀ g : ℝ → ℝ → ℕ → ℝ, (∀ k b, IsLittleO1 (g k b)) →
      ∃ g' : ℕ → ℝ, IsLittleO1 g' ∧
      ∀ (n d d' : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
        (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ beta5 →
        ∀ (Pt : Finset Ival), IsBandPartition n Pt →
        ∀ (v : Fin n → Space d) (W : Fin n → Ival → WIdx n → Space d'), BVGuarantee G Pt v W →
        ∀ (r : Fin n) (P : Ival), P ∈ Pt →
          let S := band (gram v) r P
          let Y := gram (W r P)
          ((εthr / 2 * S.card : ℝ) ≤
              ((if P.Positive then sPrimePos S Y (tauPos P εthr)
                else sPrimeNeg S Y (tauNeg P εthr)).card : ℝ)) ∧
          (P.Positive → P.rhoP ≤ 1 / 4 →
            let S' := sPrimePos S Y (tauPos P εthr)
            let S'' := S' \ isolatedIn G S'
            let τ := tauPos P εthr
            ∀ βp : ℝ, 0 < βp → βp ≤ 1 → (maxDegOn G S'' : ℝ) ≤ (S''.card : ℝ) ^ βp →
            ∀ I' : Finset (Fin n), VCMeets g h (1 / τ) G S'' I' →
              IsIndep G (isolatedIn G S' ∪ I') ∧
              (εthr * S.card) ^ (2 * τ * (1 + βp) / (2 * τ + βp) - K * h - g' S.card) ≤
                ((isolatedIn G S' ∪ I').card : ℝ)) ∧
          (P.Positive → 1 / 4 < P.rhoP →
            Edgeless G S ∧
              isolatedIn G (sPrimePos S Y (tauPos P εthr)) = sPrimePos S Y (tauPos P εthr)) ∧
          (¬ P.Positive →
            let S' := sPrimeNeg S Y (tauNeg P εthr)
            let τ := tauNeg P εthr
            ∀ βm : ℝ, 0 < βm → βm ≤ 1 → (maxDegOn G S' : ℝ) ≤ (S'.card : ℝ) ^ βm →
            ∀ I' : Finset (Fin n), VCMeets g h ((3 * τ - 1) / (2 * τ - 1)) G S' I' →
              IsIndep G I' ∧
              (εthr * S.card) ^
                  (2 * (1 + βm) * (2 * τ - 1) / ((4 + 3 * βm) * τ - (2 + βm)) - K * h - g' S.card) ≤
                (I'.card : ℝ)) := by sorry

end GaussLocalMaxColoring.Main
