-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_43
-- name    : GaussLocalMaxColoring.Main.lemma_43
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:23:52.896213+00:00
-- url     : https://prove2.me/theorems/9dd701b2-0358-4a1e-8c44-e235d905906a
-- title:
--   Lemma 43 — improved single-step lifting: a $(Ut,q)$-cover lifts to a $((U+\frac1{3000})t,\,q-t^{-100})$-cover
-- statement:
--   Section 5 setting under the analysis convention (exact edge constraint), any nested core sequence $V=F_0\supseteq F_1\supseteq\cdots$, any root $r$, and $n$ (hence $t$) sufficiently large. Let $1\le j\le\ell$ and $W\subseteq F_j$ (fixed independently of $g$), and suppose $\{u_x\}_{x\in W}$ is a $(Ut,q)$-cover for some $0<U\le\sqrt H$. Assume $p_{F_{j-1}}(x)\le e^{-t^2/2}$ and $\mathbb P_g[M_{F_{j-1}}(x)>1.968t]\le t^{-4}\overline\Phi(t/2)$ for every $x\in W$, and set $W'=N_{F_{j-1}}(W)$. Then $\{u_y\}_{y\in W'}$ is a $((U+1/3000)t,\ q-t^{-100})$-cover.
--
--   Differences from the source:
--   - generalization: the cores F₀ ⊇ ⋯ ⊇ F_ℓ produced by Algorithm 2 → any ℕ-indexed nested sequence F with F 0 = V; reason: the lemma's proof uses only the stated hypotheses on the cores; Algorithm 2's cores extended by F_j = F_ℓ for j > ℓ are an instance
--   - reading: "for sufficiently large t" (t = √((1−β) log n), Table 3) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before every graph, vector family, core sequence and parameter; reason: the asymptotic convention of the paper (uniform thresholds); t is increasing in n
--   - encoding: §5 analysis convention: the edge constraint of Lemma 34 is treated as exact (p. 35) → ExactSDPVectors G v: unit vectors, −1/2 ≤ ⟨v_i, v_j⟩ ≤ 1, ⟨v_i, v_j⟩ = −1/2 on edges, the third constraint of Lemma 34; reason: the analysis of §5.4–5.5 is stated under this convention (justified in Appendix B.2)
--   - generalization: §5 analysis convention also treats Γ_rx(X) ⪰ 0 as exact → no Γ hypothesis; reason: the proof (via Lemmas 44, 45, 39, 29, 30) does not use Γ; the convention's setting is an instance
--   - encoding: {u_y}_{y∈W′}, W′ = N_{F_{j−1}}(W); W fixed independently of g → Finset image of u over W.biUnion (nbr G (F (j−1))); W a Finset chosen before the probability; reason: repeated vectors do not change the maximum
--   - encoding: §5 standing assumptions (G 3-colorable, every degree ≤ n^β, β = 0.692601; Table 3 parameters as functions of n) → binders G.Colorable 3, maxDegOn G univ ≤ n^beta5, and the Table 3 definitions of the Section5 module; reason: the section states them once (pp. 31, 35); they are hypotheses of every §5 lemma
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
--   - encoding: vectors in R^d, g ∼ N(0, I_d), P_g → Space d = EuclideanSpace ℝ (Fin d), any d, Mathlib stdGaussian (gaussProb); reason: Lean convention; same instances
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 43, printed p. 48 (PDF 50)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Bands

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 43** (Improved single-step lifting; p. 48, PDF 50). Section 5 setting (analysis
convention: exact edge constraint), any nested core sequence, any root `r`, and `n` (hence `t`)
sufficiently large. Let `1 ≤ j ≤ ℓ` and `W ⊆ F_j` (fixed independently of `g`), and suppose
`{u_x}_{x ∈ W}` is a `(Ut, q)`-cover for some `0 < U ≤ √H`. Assume `p_{F_{j−1}}(x) ≤ e^{−t²/2}`
and `P_g[M_{F_{j−1}}(x) > 1.968t] ≤ t^{−4}Φ̄(t/2)` for every `x ∈ W`, and set
`W′ = N_{F_{j−1}}(W)`. Then `{u_y}_{y ∈ W′}` is a `((U + 1/3000)t, q − t^{−100})`-cover. -/
theorem lemma_43 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ (d : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
      (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ beta5 →
      ∀ v : Fin n → Space d, ExactSDPVectors G v →
      ∀ F : ℕ → Finset (Fin n), F 0 = Finset.univ → (∀ i, F (i + 1) ⊆ F i) →
      ∀ (r : Fin n) (j : ℕ), 1 ≤ j → j ≤ numLevels n →
      ∀ W : Finset (Fin n), W ⊆ F j →
      ∀ U q : ℝ, 0 < U → U ≤ Real.sqrt H5 →
      IsCover (W.image (uvec v r)) (U * t5 n) q →
      (∀ x ∈ W, pLocal G v (F (j - 1)) x ≤ Real.exp (-(t5 n ^ 2 / 2)) ∧
        gaussProb {g : Space d |
            ((1968 / 1000 * t5 n : ℝ) : WithBot ℝ) < nbrMax G v (F (j - 1)) x g} ≤
          (t5 n ^ 4)⁻¹ * PhiTail (t5 n / 2)) →
      IsCover ((W.biUnion (nbr G (F (j - 1)))).image (uvec v r)) ((U + 1 / 3000) * t5 n)
        (q - (t5 n ^ 100)⁻¹) := by sorry

end GaussLocalMaxColoring.Main
