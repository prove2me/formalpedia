-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_theorem_3_9
-- name    : GrothendieckLB.Supplement.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:42:27.664858+00:00
-- url     : https://prove2.me/theorems/2ef45e25-06fa-4b67-be68-885fa942dcc7
-- title:
--   Theorem 3.9: $K_G\le\pi/(2\gamma)$ from a limiting Krivine scheme
-- statement:
--   Let $S=(f,g,\rho_1,\dots,\rho_k)$ be a limiting Krivine scheme with correlation function $H$, and suppose $H'(0)\ne0$, so that $H$ has a local holomorphic inverse at the origin. Write
--   $$
--   H^{-1}(z)=\sum_{j\ge0}a_{2j+1}z^{2j+1},\qquad M(r)=\sum_{j\ge0}|a_{2j+1}|\,r^{2j+1}.
--   $$
--   If $\gamma>0$ lies within the radius of convergence of $H^{-1}$ and $M(\gamma)=1$, then
--   $$
--   K_G\le\frac{\pi}{2\gamma}.
--   $$
--
--   This is the upper-bound machinery of the paper: a limiting scheme with a good inverse majorant bounds the Grothendieck constant.
--
--   **Formalization Note** $K_G$ is the published `grothendieckConst`. The local inverse is the base `IsLocalInverseBranch` with Taylor coefficients $a_n$; "$\gamma$ within the radius of convergence" is $\sum_n|a_n|R^n<\infty$ for some $R>\gamma$.
--
--   Differences from the source:
--   - reading: γ > 0 within the radius of convergence of H⁻¹ → ∑ |a_n| R^n converges for some R > γ (γ strictly less than the radius); reason: 'within' read as strictly inside the disk of convergence, which is what the proof (Lemma 3.10, 0 < γ < R₀) uses
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 3.9, p.21

import Mathlib
import Definitions.Def_GrothendieckConstantDefs
import Definitions.Def_GrothendieckLB_IsLocalInverseBranch
import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_LimitingScheme_corr

namespace GrothendieckLB

namespace Supplement

/-- Theorem 3.9, upper bound from a limiting Krivine scheme (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 3.9, p.21): let
`S = (f, g, ρ₁, …, ρ_k)` be a limiting Krivine scheme with correlation function `H`, and suppose
`H′(0) ≠ 0`, so that `H` has a local holomorphic inverse at the origin. Write
`H⁻¹(z) = ∑_{j ≥ 0} a_{2j+1} z^{2j+1}` and `M(r) = ∑_{j ≥ 0} |a_{2j+1}| r^{2j+1}`. If there exists
`γ > 0`, within the radius of convergence of `H⁻¹`, such that `M(γ) = 1`, then `K_G ≤ π/(2γ)`.

**Formalization Note** `K_G` is the published `GrothendieckConstant.grothendieckConst`. `G` is the
local inverse branch (base `IsLocalInverseBranch`) and `a_n = taylorCoeff n G`. "`γ` within the
radius of convergence" is `∑ |a_n| R^n < ∞` for some `R > γ` (i.e. `γ` strictly inside the disk of
convergence); it makes the series `M(γ)` converge. `M` runs over odd indices, as printed. -/
theorem theorem_3_9 {k : ℕ} (S : LimitingScheme k) (hderiv : deriv S.corr 0 ≠ 0) (G : ℝ → ℝ)
    (hG : IsLocalInverseBranch S.corr G) (γ : ℝ) (hγ : 0 < γ)
    (hrad : ∃ R : ℝ, γ < R ∧ Summable (fun n => |taylorCoeff n G| * R ^ n))
    (hM : ∑' j : ℕ, |taylorCoeff (2 * j + 1) G| * γ ^ (2 * j + 1) = 1) :
    GrothendieckConstant.grothendieckConst ≤ Real.pi / (2 * γ) := by sorry

end Supplement

end GrothendieckLB
