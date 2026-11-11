-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_21
-- name    : GaussLocalMaxColoring.Main.lemma_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:22:05.135573+00:00
-- url     : https://prove2.me/theorems/1eff0dd3-fe5f-4af4-8cd8-0113330e581c
-- title:
--   Lemma 21 — with probability $\ge 3/4$ all empirical local-maximum frequencies are within $\delta/8$, hence $p_{F_{j-1}}(x)<\delta$ on $F_j$
-- statement:
--   Consider one trial of Algorithm 2 on a graph $G$ with vectors $\{v_x\}$, $\delta\in(0,1)$, any target $T$ and $R=\lceil32\delta^{-2}\log(8n\ell)\rceil$ samples per level, $\ell=\lceil\log n\rceil$. With probability at least $3/4$ over its $\ell R$ i.i.d. standard Gaussian samples: for every level $j$ at which $F_j$ is constructed (no sampled set of size $\ge T$ at levels $1,\dots,j$) and every $x\in F_{j-1}$, $|\hat p_j(x)-p_{F_{j-1}}(x)|\le\delta/8$; and (in particular) $p_{F_{j-1}}(x)<\delta$ for every such $j$ and every $x\in F_j$.
--
--   Differences from the source:
--   - generalization: §4 high-degree setting (Table 2 parameters, strict vector 3-coloring) → any graph, any vectors, any δ ∈ (0, 1), any T, with R = ⌈32δ⁻²log(8nℓ)⌉ ("by the choice of R"); reason: the proof uses only Hoeffding and the formula for R; Table 2 (high degree), Table 3 and Appendix A are instances
--   - encoding: "with probability at least 3/4 over the samples used to construct the cores … in particular …" → the product Gaussian law (trialLaw) of the event "first claim ∧ second claim"; reason: the second claim follows from the first on every sample; stating both inside the event keeps both
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
--   - encoding: vectors in R^d, g ∼ N(0, I_d), P_g → Space d = EuclideanSpace ℝ (Fin d), any d, Mathlib stdGaussian (gaussProb); reason: Lean convention; same instances
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 21, printed p. 19 (PDF 21)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Iterative

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 21** (p. 19, PDF 21), for one trial of Algorithm 2 with any graph, any vectors, any
`δ ∈ (0, 1)`, any `T` and `R = ⌈32 δ^{−2} log(8nℓ)⌉`: with probability at least `3/4` over the
`ℓR` Gaussian samples, `|p̂_j(x) − p_{F_{j−1}}(x)| ≤ δ/8` for every level `j` at which `F_j` is
constructed and every `x ∈ F_{j−1}`, and (in particular) `p_{F_{j−1}}(x) < δ` for every such `j`
and every `x ∈ F_j`. -/
theorem lemma_21 {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (T : ℕ) :
    (trialLaw n d ⌈32 * δ⁻¹ ^ 2 * Real.log (8 * n * (numLevels n : ℝ))⌉₊).real
        {ω | ∀ j, 1 ≤ j → j ≤ numLevels n → Constructed G v δ T ω j →
          (∀ x ∈ cores G v δ ω (j - 1),
            |phat G v δ ω j x - pLocal G v (cores G v δ ω (j - 1)) x| ≤ δ / 8) ∧
          (∀ x ∈ cores G v δ ω j, pLocal G v (cores G v δ ω (j - 1)) x < δ)} ≥ 3 / 4 := by sorry

end GaussLocalMaxColoring.Main
