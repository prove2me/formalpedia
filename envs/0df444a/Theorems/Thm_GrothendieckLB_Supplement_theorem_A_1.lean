-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_theorem_A_1
-- name    : GrothendieckLB.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:44:28.09548+00:00
-- url     : https://prove2.me/theorems/3d7de157-6050-4271-8fc0-657a24e9e050
-- title:
--   Theorem A.1: Krivine preprocessing and projection, $K_G\le\pi/(2\gamma)$
-- statement:
--   Let $f,g:\mathbb R^k\to\{-1,1\}$ be odd measurable functions with arcsine-normalized correlation function
--   $$
--   H(t)=\frac\pi2\,\mathbb E\Bigl[f(G_1)\,g\bigl(tG_1+\sqrt{1-t^2}\,G_2\bigr)\Bigr],\qquad -1<t<1,
--   $$
--   where $G_1,G_2$ are independent standard Gaussian vectors in $\mathbb R^k$. Suppose that $H$ has a local inverse at the origin, $H^{-1}(\zeta)=\sum_{r\ge1}a_r\zeta^r$, which is holomorphic on a neighborhood of $\gamma\overline{\mathbb D}$, and that
--   $$
--   \sum_{r\ge1}|a_r|\,\gamma^r\le1 .
--   $$
--   Then
--   $$
--   K_G\le\frac{\pi}{2\gamma}.
--   $$
--
--   This is Krivine's preprocessing-and-projection argument for one ordinary scheme; Krivine's bound is its special case for the hyperplane scheme.
--
--   **Formalization Note** $(f,g)$ is the published `KrivineScheme k` and $H$ its `correlationFunction` (the pair $(G_1,tG_1+\sqrt{1-t^2}G_2)$ has coordinatewise correlation $t$). "Holomorphic on a neighborhood of $\gamma\overline{\mathbb D}$" is $\sum_r|a_r|R^r<\infty$ for some $R>\gamma$. $K_G$ is the published `grothendieckConst`.
--
--   Differences from the source:
--   - encoding: γ D with γ > 0 implicit (a disk of radius γ) → explicit hypothesis 0 < γ; reason: the page's γD is a disk only for γ > 0; at γ = 0 the hypotheses hold trivially and π/0 = 0 in Lean, so the condition only excludes the undefined case
--   - encoding: H⁻¹ holomorphic on a neighborhood of γD → ∑ |a_r| R^r converges for some R > γ; reason: a neighborhood of the compact disk γD contains a disk of radius R > γ, and conversely; same instances
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem A.1, p.47

import Mathlib
import Definitions.Def_GrothendieckConstantDefs
import Definitions.Def_KrivineSchemeDefs
import Definitions.Def_GrothendieckLB_IsLocalInverseBranch
import Definitions.Def_GrothendieckLB_taylorCoeff

namespace GrothendieckLB

namespace Supplement

/-- Theorem A.1, Krivine preprocessing and projection (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem A.1, p.47): let
`f, g : ℝ^k → {−1, 1}` be odd measurable functions with arcsine-normalized correlation function
`H(t) = (π/2) E[f(G₁) g(tG₁ + √(1 − t²) G₂)]`, `−1 < t < 1`. Suppose that `H` has a local inverse
at the origin, `H⁻¹(ζ) = ∑_{r ≥ 1} a_r ζ^r`, holomorphic on a neighborhood of `γD`, and
`∑_{r ≥ 1} |a_r| γ^r ≤ 1`. Then `K_G ≤ π/(2γ)`.

**Formalization Note** `(f, g)` is the published `GrothendieckConstant.KrivineScheme k` (oddness
almost everywhere) and `H` its `correlationFunction`: `(G₁, tG₁ + √(1 − t²)G₂)` is a pair of standard
Gaussian vectors with coordinatewise correlation `t`, whose density is the published
`gaussianPairDensity k t`. `G` is a local inverse branch (base `IsLocalInverseBranch`),
`a_r = taylorCoeff r G`. "Holomorphic on a neighborhood of `γD`" is `∑ |a_r| R^r < ∞` for some
`R > γ`. `γ > 0` is implicit in "`γD`" and is a hypothesis. -/
theorem theorem_A_1 {k : ℕ} (S : GrothendieckConstant.KrivineScheme k) (G : ℝ → ℝ)
    (hG : IsLocalInverseBranch (GrothendieckConstant.correlationFunction S) G) (γ : ℝ)
    (hγ : 0 < γ) (hhol : ∃ R : ℝ, γ < R ∧ Summable (fun r => |taylorCoeff r G| * R ^ r))
    (hM : ∑' r : ℕ, |taylorCoeff (r + 1) G| * γ ^ (r + 1) ≤ 1) :
    GrothendieckConstant.grothendieckConst ≤ Real.pi / (2 * γ) := by sorry

end Supplement

end GrothendieckLB
