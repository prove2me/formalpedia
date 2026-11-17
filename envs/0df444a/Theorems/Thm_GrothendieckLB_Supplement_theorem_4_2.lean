-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_theorem_4_2
-- name    : GrothendieckLB.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:43:07.743621+00:00
-- url     : https://prove2.me/theorems/dfcd24e8-5183-470e-b72d-5bebbaef3484
-- title:
--   Theorem 4.2 (= Theorem 6.4): cubic–quintic upper bound $K_G\le1.7818666069360661$
-- statement:
--   Let $H$ be the correlation function of the cubic–quintic limiting scheme (Definition 4.1) with parameters
--   $$
--   \eta=0.136419125,\qquad s_3=0.34101124,\qquad s_5=0.05276111,
--   $$
--   and let $M(r)=\sum_{n\ge1}|a_n|r^n$ be the inverse majorant of $H$, where $H^{-1}(z)=\sum_{n\ge1}a_nz^n$ is its local inverse at the origin. At $\gamma=0.881545409$ we have $M(\gamma)<1$. Consequently
--   $$
--   K_G\le\frac{\pi}{2\gamma}\le1.7818666069360661<\frac{\pi}{2\log(1+\sqrt2)}-3.4737\cdot10^{-4}.
--   $$
--
--   This is the paper's upper bound: it improves Krivine's bound $\pi/(2\log(1+\sqrt2))$ by more than $3.4737\cdot10^{-4}$. Theorem 6.4 (p.29) is the same statement without the last inequality.
--
--   **Formalization Note** All decimals are exact rational constants. The local inverse of $H$ is asserted to exist, and $M(\gamma)<1$ (with convergence of the series) is asserted for every local inverse branch, all of which share the same germ. $K_G$ is the published `grothendieckConst`.
--
--   Differences from the source:
--   - reading: Let M be the inverse majorant of H (presupposes the local inverse of H) → existence of a local inverse branch is a conjunct; M(γ) < 1 holds for every local inverse branch; reason: makes the presupposition explicit, so the M(γ) clause cannot hold vacuously; p.26 states the inverse exists because H′(0) = b₁ > 0
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 4.2, p.24; Theorem 6.4, (32), p.29

import Mathlib
import Definitions.Def_GrothendieckConstantDefs
import Definitions.Def_GrothendieckLB_IsLocalInverseBranch
import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_cqCorr

namespace GrothendieckLB

namespace Supplement

/-- Theorem 4.2 (= Theorem 6.4), cubic–quintic upper bound (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 4.2, p.24; Theorem 6.4,
(32), p.29): let `H` be the correlation function of the cubic–quintic limiting scheme with the
parameters (10), `η = 0.136419125`, `s₃ = 0.34101124`, `s₅ = 0.05276111`, and `M` the inverse
majorant of `H`. At `γ = 0.881545409`, `M(γ) < 1`. Consequently
`K_G ≤ π/(2γ) ≤ 1.7818666069360661 < π/(2 log(1 + √2)) − 3.4737 · 10⁻⁴`.

**Formalization Note** `H = cqCorr η s₃ s₅` (Definition 4.1, (13)). The local inverse exists
(`H′(0) = b₁ > 0`, p.26) and is stated to exist; for every local inverse branch `G`
(base `IsLocalInverseBranch`, unique germ) with `a_n = taylorCoeff n G`, the majorant
`M(γ) = ∑_{n ≥ 1} |a_n| γ^n` (22) converges and is `< 1`. All decimals are exact rationals.
`K_G` is the published `GrothendieckConstant.grothendieckConst`. -/
theorem theorem_4_2 :
    (∃ G : ℝ → ℝ, IsLocalInverseBranch (cqCorr 0.136419125 0.34101124 0.05276111) G) ∧
    (∀ G : ℝ → ℝ, IsLocalInverseBranch (cqCorr 0.136419125 0.34101124 0.05276111) G →
      Summable (fun n : ℕ => |taylorCoeff (n + 1) G| * (0.881545409 : ℝ) ^ (n + 1)) ∧
      ∑' n : ℕ, |taylorCoeff (n + 1) G| * (0.881545409 : ℝ) ^ (n + 1) < 1) ∧
    GrothendieckConstant.grothendieckConst ≤ Real.pi / (2 * 0.881545409) ∧
    Real.pi / (2 * 0.881545409) ≤ (1.7818666069360661 : ℝ) ∧
    (1.7818666069360661 : ℝ) <
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.4737e-4 := by sorry

end Supplement

end GrothendieckLB
