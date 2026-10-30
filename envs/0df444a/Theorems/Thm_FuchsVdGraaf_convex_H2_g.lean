-- Prove2me | Theorems.Thm_FuchsVdGraaf_convex_H2_g
-- name    : FuchsVdGraaf.convex_H2_g
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:14:35.358117+00:00
-- url     : https://prove2.me/theorems/2f5a9fa9-7a8a-4aa3-ae65-54a079f5019b
-- title:
--   Convexity of $r\mapsto H_2\big(\tfrac12 - \tfrac12\sqrt{1-r^2}\big)$ (p.19, $g$ from eq. (65))
-- statement:
--   Let $H_2$ be the binary entropy in bits and $g(r) = \tfrac12 - \tfrac12\sqrt{1-r^2}$ (eq. (65)). The function
--
--   $$
--   r \;\longmapsto\; H_2\big(g(r)\big) = H_2\Big(\tfrac12 - \tfrac12\sqrt{1-r^2}\Big)
--   $$
--
--   is convex on $[-1, 1]$.
--
--   This is the convexity fact behind the upper bound $\mathrm{SD} \le 1 - H_2\big(\tfrac12 - \tfrac12\sqrt{1-B^2}\big)$: by Jensen's inequality it lets one pass from an average of $H_2(g(\cdot))$ over outcomes to $H_2(g(\cdot))$ of the average, which is the Bhattacharyya coefficient.
--
--   Differences from the source:
--   - generalization: "$H_2(g(r))$ is a convex function", applied to values in $[0,1]$ → convex on $[-1,1]$; reason: $[-1,1]$ is the whole set where $g$ is real, and it contains $[0,1]$, so the statement specialises to the use in the proof.
--   - encoding: $\log$ in $H_2$ → `WildeQIT.binaryEntropy` with `Real.logb 2`; reason: Lean convention, same function.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, p.19 (before eq. (66)); g from eq. (65), p.18

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, p.19 (proof of Proposition 5, before
(66)), with `g` from eq. (65), p.18: the function `r ↦ H₂(g(r))`, where
`g(r) = ½ − ½ √(1 − r²)` and `H₂` is the binary entropy in bits, is convex.

**Formalization Note.** The paper names no domain. Convexity is stated on `[−1, 1]`, the set on
which `g` is real; the proof of Proposition 5 applies it to the values
`k(r₀(x)) = 2√(r₀(x)(1 − r₀(x))) ∈ [0, 1]`, a subset. `H₂` is `WildeQIT.binaryEntropy`. -/
theorem convex_H2_g :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1)
      (fun r : ℝ => WildeQIT.binaryEntropy (1 / 2 - 1 / 2 * Real.sqrt (1 - r ^ 2))) := by sorry

end FuchsVdGraaf
