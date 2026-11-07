-- Prove2me | Theorems.Thm_GrothendieckLB_proposition_9_2
-- name    : GrothendieckLB.proposition_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:52:38.338877+00:00
-- url     : https://prove2.me/theorems/a465d29d-a250-4bda-850a-2e98cb5f2618
-- title:
--   Proposition 9.2: the majorant barrier $\gamma\le11/12$
-- statement:
--   Let $H(t)=b_1t+b_3t^3+b_5t^5+\cdots$ be odd and analytic near the origin, and suppose that
--   $$
--   0<b_1\le1,\qquad b_3\ge2b_1-\frac{11}6 .
--   $$
--   Then every admissible value $\gamma$ for $H$ (Definition 9.1) satisfies
--   $$
--   \gamma\le\frac{11}{12}.
--   $$
--   This converts the affine coefficient inequality into a universal barrier for the inverse-majorant parameter.
--
--   **Formalization Note** The coefficients $b_1,b_3$ are the Taylor coefficients of $H$ at the origin.
--
--   Differences from the source: none.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Proposition 9.2, p.41

import Mathlib
import Definitions.Def_GrothendieckLB_IsAdmissible
import Definitions.Def_GrothendieckLB_taylorCoeff
open Topology

namespace GrothendieckLB

/-- Proposition 9.2, the majorant barrier (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Proposition 9.2, p.41): let
`H(t) = b₁t + b₃t³ + b₅t⁵ + ⋯` be odd and analytic near the origin with `0 < b₁ ≤ 1` and
`b₃ ≥ 2b₁ − 11/6`. Then every admissible value for `H` satisfies `γ ≤ 11/12`. -/
theorem proposition_9_2 {H : ℝ → ℝ} (hodd : ∀ᶠ t in 𝓝 (0 : ℝ), H (-t) = -H t)
    (han : AnalyticAt ℝ H 0) (hb₁ : 0 < taylorCoeff 1 H) (hb₁' : taylorCoeff 1 H ≤ 1)
    (hb₃ : 2 * taylorCoeff 1 H - 11 / 6 ≤ taylorCoeff 3 H) {γ : ℝ} (hγ : IsAdmissible H γ) :
    γ ≤ 11 / 12 := by sorry

end GrothendieckLB
