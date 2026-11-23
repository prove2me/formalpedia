-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_theorem_2_4
-- name    : GrothendieckLB.Supplement.theorem_2_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T14:41:24.010196+00:00
-- url     : https://prove2.me/theorems/3c10cedf-cc70-43e6-9f88-40efaf0e5c8e
-- title:
--   Theorem 2.4: inverse-majorant criterion $M(\gamma)\le(\gamma+\Delta_H)/b_1<1$
-- statement:
--   Let
--   $$
--   H(t)=b_1t+\sum_{\substack{m\ge3\\ m\text{ odd}}}b_mt^m,\qquad b_1>0,\qquad \Delta_H:=\sum_{\substack{m\ge3\\ m\text{ odd}}}|b_m|<\infty .
--   $$
--   Let $H^{-1}(\zeta)=\sum_{n\ge1}a_n\zeta^n$ be the local inverse of $H$ at the origin and $M(r)=\sum_{n\ge1}|a_n|r^n$ its majorant. If $\gamma>0$ satisfies $\gamma+\Delta_H<b_1$, then
--
--   1. $H^{-1}$ extends analytically to a disk of radius greater than $\gamma$, and
--   2. $M(\gamma)$ converges and
--   $$
--   M(\gamma)\le\frac{\gamma+\Delta_H}{b_1}<1 .
--   $$
--
--   The criterion reduces an inverse-majorant certificate to a lower bound on $b_1$ and an upper bound on the nonlinear mass $\Delta_H$.
--
--   **Formalization Note** $H$ is any real function equal to the series on $(-1,1)$; the local inverse is the base mission's `IsLocalInverseBranch` and $a_n$ its Taylor coefficients. "Extends analytically to a disk of radius greater than $\gamma$" is stated as $\sum_n|a_n|R^n<\infty$ for some $R>\gamma$, which is equivalent to the Taylor series of $H^{-1}$ at $0$ having radius of convergence greater than $\gamma$.
--
--   Differences from the source:
--   - encoding: H⁻¹ extends analytically to a disk of radius greater than γ → ∑ |a_n| R^n converges for some R > γ; reason: equivalent to the Taylor series of H⁻¹ at 0 having radius of convergence > γ, i.e. to a holomorphic extension to a disk of radius > γ; same instances
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 2.4, p.11

import Mathlib
import Definitions.Def_GrothendieckLB_IsLocalInverseBranch
import Definitions.Def_GrothendieckLB_taylorCoeff

namespace GrothendieckLB

namespace Supplement

/-- Theorem 2.4, inverse-majorant criterion (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 2.4, p.11): let
`H(t) = b₁t + ∑_{m ≥ 3, m odd} b_m t^m` with `b₁ > 0` and `ΔH := ∑_{m ≥ 3, m odd} |b_m| < ∞`. If
`γ > 0` satisfies `γ + ΔH < b₁`, then the local inverse `H⁻¹` extends analytically to a disk of
radius greater than `γ`, and its majorant satisfies `M(γ) ≤ (γ + ΔH)/b₁ < 1`.

**Formalization Note** The coefficients are a sequence `b : ℕ → ℝ` vanishing at even indices, so
`ΔH = ∑' m, |b (m + 2)|`. `H` is any real function equal to the series on `(−1, 1)` (the series
converges absolutely there). `G` is the local inverse branch (base `IsLocalInverseBranch`) with
Taylor coefficients `a_n = taylorCoeff n G`. "Extends analytically to a disk of radius `R > γ`" is
written as absolute summability of `∑ |a_n| R^n` for some `R > γ`, which is equivalent to the
Taylor series of `H⁻¹` at `0` having radius of convergence `> γ`. `M(γ) = ∑_{n ≥ 1} |a_n| γ^n`. -/
theorem theorem_2_4 (b : ℕ → ℝ) (hb_even : ∀ m, Even m → b m = 0) (hb₁ : 0 < b 1)
    (hb_sum : Summable (fun m => |b m|)) (H : ℝ → ℝ)
    (hH : ∀ t : ℝ, |t| < 1 → H t = ∑' m, b m * t ^ m) (G : ℝ → ℝ)
    (hG : IsLocalInverseBranch H G) (γ : ℝ) (hγ : 0 < γ)
    (hgap : γ + ∑' m, |b (m + 2)| < b 1) :
    (∃ R : ℝ, γ < R ∧ Summable (fun n => |taylorCoeff n G| * R ^ n)) ∧
      Summable (fun n => |taylorCoeff (n + 1) G| * γ ^ (n + 1)) ∧
      ∑' n, |taylorCoeff (n + 1) G| * γ ^ (n + 1) ≤ (γ + ∑' m, |b (m + 2)|) / b 1 ∧
      (γ + ∑' m, |b (m + 2)|) / b 1 < 1 := by sorry

end Supplement

end GrothendieckLB
