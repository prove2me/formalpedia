-- Prove2me | Theorems.Thm_NodeStableProj_Main_app_C_size_estimate
-- name    : NodeStableProj.Main.app_C_size_estimate
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:57:58.974762+00:00
-- url     : https://prove2.me/theorems/c2070147-dbe5-4181-9283-6b7590ed5118
-- title:
--   App. C — the truncated discrete Laplace size estimate: deterministic bounds, endpoint masses, and (ε_s, δ_s)-indistinguishability
-- statement:
--   Let $\varepsilon_s>0$, $\delta_s\in(0,1)$, $B=\lceil(1/\varepsilon_s)\log(4/\delta_s)\rceil$, and let $Z$ be the discrete Laplace law with parameter $\varepsilon_s$ conditioned on $|Z|\le B$. For a graph with $s$ vertices:
--   1. deterministically (for every $z\in[-B,B]$), $\max\{1,s\}\le\hat n=\max\{1,s+B+z\}\le s+2B$;
--   2. the endpoint masses satisfy $\Pr[Z=-B],\Pr[Z=B]\le e^{-\varepsilon_sB}$, and $e^{-\varepsilon_sB}\le\delta_s/4$;
--   3. before clamping, the estimate is $(\varepsilon_s,\delta_s)$-indistinguishable for sizes differing by one:
--   $$s+B+Z\ \approx_{\varepsilon_s,\delta_s}\ (s+1)+B+Z .$$
--
--   This is the first stage of the wrapper of Theorem 3.5, which releases a private upper estimate of the number of vertices. The order claim $|V|+2B=|V|+O(\log(1/\delta)/\varepsilon)$ of the same sentence is the companion item `NodeStableProj.Main.app_C_size_estimate_order`.
--
--   Differences from the source:
--   - reading: "under node-neighboring changes" → the estimates for sizes s and s + 1, every s ∈ ℕ; reason: node-neighbouring graphs have sizes differing by one; the estimate depends on the size only
--   - encoding: log in B → natural logarithm; reason: base immaterial; natural log makes e^{−ε_s B} ≤ δ_s/4 exact
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 33, Appendix C (proof of Theorem 3.5), the size estimate

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_NodeStableProj_Main_SizeEstimate

open MeasureTheory

namespace NodeStableProj.Main

/-- Appendix C, p. 33: with `B = ⌈(1/ε_s) log(4/δ_s)⌉` and `Z` the discrete Laplace law with
parameter `ε_s` conditioned on `|Z| ≤ B`, for a graph with `s` vertices:
(1) deterministically `max{1, s} ≤ n̂ = max{1, s + B + Z} ≤ s + 2B`;
(2) the endpoint masses `Pr[Z = ±B]` are at most `e^{−ε_s B}`, and `e^{−ε_s B} ≤ δ_s/4`;
(3) `s + B + Z ≈_{ε_s,δ_s} (s + 1) + B + Z`. -/
theorem app_C_size_estimate (εs δs : ℝ) (hεs : 0 < εs) (hδs0 : 0 < δs) (hδs1 : δs < 1)
    (s : ℕ) :
    (∀ z ∈ Finset.Icc (-(sizeB εs δs : ℤ)) (sizeB εs δs),
      max 1 (s : ℤ) ≤ max 1 ((s : ℤ) + sizeB εs δs + z) ∧
        max 1 ((s : ℤ) + sizeB εs δs + z) ≤ (s : ℤ) + 2 * sizeB εs δs) ∧
    (truncDiscreteLaplace εs (sizeB εs δs) {-(sizeB εs δs : ℤ)} ≤
        ENNReal.ofReal (Real.exp (-εs * sizeB εs δs)) ∧
      truncDiscreteLaplace εs (sizeB εs δs) {(sizeB εs δs : ℤ)} ≤
        ENNReal.ofReal (Real.exp (-εs * sizeB εs δs)) ∧
      Real.exp (-εs * sizeB εs δs) ≤ δs / 4) ∧
    PFRelease.Indist (sizeEstimateLaw εs δs s) (sizeEstimateLaw εs δs (s + 1)) εs δs := by sorry

end NodeStableProj.Main
