-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_expected_maxcut_sampling_error
-- name    : MaxCutMatrix2027.Upper.expected_maxcut_sampling_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T12:48:15.647478+00:00
-- url     : https://prove2.me/theorems/29da6dc3-665f-4052-b7de-b61bbbe8ae5a
-- title:
--   Theorem 4.2 — Expected normalized MAX-CUT sampling error
-- statement:
--   There is one absolute constant $C_0>0$ such that for every simple graph $G$ on $n$ vertices and every real $1\le s\le n$, the independently sampled vertex set $Q$ with inclusion probability $s/n$ satisfies
--   $$\mathbb E\left|\frac{\operatorname{MAXCUT}(G[Q])}{s^2}-\frac{\operatorname{MAXCUT}(G)}{n^2}\right|\le\frac{C_0}{\sqrt s}.$$
--   This uses the uncapped Bernoulli set, including empty and singleton outcomes, and the square of the real expected size. It is not a fixed-cardinality or with-replacement sample. The constant is uniform over $n,G,s$; the proof gives $C_0=(3C_{\mathrm{res}}+29)/4$. This is the accuracy estimate used to analyze Algorithm 1.
--
--   Differences from the source:
--   - encoding: vertices labelled by [n] and independent Bernoulli selectors → Fin n and the exact finite Bernoulli-subset expectation; reason: relabeling is bijective and the subset weights are exactly the independent-selector law
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Theorem 4.2, p.17 (PDF p.17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
set_option autoImplicit false

namespace MaxCutMatrix2027.Upper

/-- Theorem 4.2, p.17. Real expected sample size, uncapped independent vertex sample. -/
theorem expected_maxcut_sampling_error :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℝ),
      1 ≤ s → s ≤ n →
      sampleAverage (s / n) (fun Q =>
        |inducedMaxCut G Q / s ^ 2 - (IIDMatchHard.maxCut G : ℝ) / (n : ℝ) ^ 2|) ≤
      C₀ / Real.sqrt s := by sorry

end MaxCutMatrix2027.Upper
