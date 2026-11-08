-- Prove2me | Theorems.Thm_HardcoreSlices_theorem_2_4
-- name    : HardcoreSlices.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:41.845725+00:00
-- url     : https://prove2.me/theorems/c242d664-0436-49ce-9ce4-2f85c867984f
-- title:
--   Theorem 2.4 — near-Ramanujan: $\lambda_2(A_G)\le2\sqrt{\Delta-1}+o(1)$ (corrected: $\Delta\ge2$)
-- statement:
--   Let $G$ be a uniformly random $\Delta$-regular bipartite graph with sides of size $m$, for fixed $\Delta\ge2$. Then for every $\varepsilon>0$, with probability tending to $1$ as $m\to\infty$,
--   $$\lambda_2(A_G)\le2\sqrt{\Delta-1}+\varepsilon.$$
--   This is the spectral input to both slice expansion theorems: it bounds the top-link eigenvalues of Lemmas 4.1 and 5.1.
--
--   Differences from the source:
--   - correction: ∆ > 0 implicit → ∆ ≥ 2; reason: at ∆ = 1 the graph is a perfect matching, with λ2 = 1 > 0 + o(1)
--   - encoding: + o(1) in n → for every ε > 0, + ε with high probability; reason: the same statement for fixed ∆
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Theorem 2.4, p.10

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting
import Definitions.Def_HardcoreSlices_lam2

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Theorem 2.4 ([Fri03]).** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.10: "Let `G = (X, Y, E)` be a random `∆`-regular bipartite graph on `n` vertices. Then with
high probability `λ2(AG) ≤ 2√(∆ − 1) + o(1)`."

**Formalization Note.** Corrected to `∆ ≥ 2`: at `∆ = 1` the graph is a perfect matching and `λ2 = 1 > 0 + o(1)`. The
`o(1)` is in the number of vertices, for fixed `∆`, so it is a statement for every `ε > 0`. -/
theorem theorem_2_4 (Δ : ℕ) (hΔ : 2 ≤ Δ) (ε : ℝ) (hε : 0 < ε) :
    AlmostEvery Δ (fun _ G => lam2 G ≤ 2 * Real.sqrt ((Δ : ℝ) - 1) + ε) := by sorry

end HardcoreSlices
