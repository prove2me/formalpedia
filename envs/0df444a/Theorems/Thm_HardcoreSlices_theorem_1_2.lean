-- Prove2me | Theorems.Thm_HardcoreSlices_theorem_1_2
-- name    : HardcoreSlices.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:51.580142+00:00
-- url     : https://prove2.me/theorems/9cdd86a5-905a-46a9-8baa-4cdfba38e2d6
-- title:
--   Theorem 1.2 — trickle-down and the mixing time of the down-up walk
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $(X,\mu)$ be a pure $d$-dimensional complex with a distribution $\mu$ positive on its facets, with $d\ge2$ and $\delta\in(0,1]$. If $(X,\mu)$ is a connected $\frac{1-\delta}d$-top-link spectral expander, then:
--
--   1. $X$ is a $\frac{1-\delta}{\delta d}$-local spectral expander;
--   2. for every $\varepsilon>0$ and every time $t\ge C\frac d\delta\log\frac1{\varepsilon\min_{\tau\in X(d)}\mu(\tau)}$, the down-up walk from any facet is within total variation $\varepsilon$ of $\mu$.
--
--   This converts the top-link bounds of Theorems 1.8 and 1.9 into polynomial mixing.
--
--   **Formalization Note** Dimension is cardinality. "Connected" is the link-connectedness in `HDXConc.IsTopLinkExpander`.
--
--   Differences from the source:
--   - encoding: λ2(Pτ) ≤ b → HDXConc.SecondEigLE in Rayleigh form; reason: equivalent by Courant–Fischer for a reversible walk on at least two vertices, with no eigenvalue sort
--   - encoding: mixes to total variation ε in time O(…) → ∃ absolute C, every t ≥ C(d/δ)log(…), every start; reason: the implied constant is absolute; the distance to stationarity does not increase with t
--   - encoding: µ a distribution on X(d), with min µ(τ) in the time bound → µ positive on every facet (HDXConc.IsTopDensity); reason: with a zero mass the printed time log(1/(ε·0)) is infinite and the claim says nothing; only those instances are excluded
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Theorem 1.2, p.1

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_faces
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_mm_mixing
import Definitions.Def_HardcoreSlices_downUp

open Classical

namespace HardcoreSlices

/-- **Theorem 1.2 ([DK17, Opp18, AL20]).** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.1: "If `(X, µ)` is a connected `d`-dimensional `(1−δ)/d`-top-link spectral expander for
`δ ∈ (0, 1]` and `d ≥ 2` then `X` is a `(1−δ)/(δd)`-local spectral expander. Moreover, the down-up walk mixes to total variation
distance `ε > 0` in time `O((d/δ) log(1/(ε min_{τ∈X(d)} µ(τ))))`."

**Formalization Note.** The implied constant `C` is absolute, chosen before the complex. Dimension is cardinality (p.1, footnote 1).
`HDXConc.IsTopLinkExpander` packages the top-link bound and the connectedness of the links of faces with at most `d − 2` vertices,
including `∅`. `π` is a density on `X(d)`, positive on every facet. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) (δ : ℝ)
      (π : Finset V → ℝ), SteurerHDX.IsPure X d → HDXConc.IsTopDensity X d π → 2 ≤ d → 0 < δ → δ ≤ 1 →
      HDXConc.IsTopLinkExpander X d π ((1 - δ) / d) →
      (∀ s ∈ X, s.card + 2 ≤ d →
        HDXConc.SecondEigLE (HDXConc.linkVerts X s) (HDXConc.linkWeight X d π s) ((1 - δ) / (δ * d))) ∧
      ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, C * ((d : ℝ) / δ) * Real.log (1 / (ε * muMin X d π)) ≤ t →
        ∀ σ : {σ // σ ∈ SteurerHDX.faces X d},
          MarkovMixing.tvDist (MarkovMixing.rowDist (downUp X d π) t σ) (fun σ' => π σ'.1) ≤ ε := by sorry

end HardcoreSlices
