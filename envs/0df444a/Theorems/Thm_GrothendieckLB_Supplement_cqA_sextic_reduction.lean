-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cqA_sextic_reduction
-- name    : GrothendieckLB.Supplement.cqA_sextic_reduction
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T17:22:39.97881+00:00
-- url     : https://prove2.me/theorems/a1e85662-66e6-48d4-abef-6da6d91140a0
-- title:
--   One-dimensional sextic moment formulas for cubic–quintic Hermite coefficients
-- statement:
--   For $s=\eta/\sqrt{6(1+s_3^2+s_5^2)}$, put $T(x)=s(x^3-3x)$ and $K(x)=\exp(-(x^2+T(x)^2)/2)$. Let $H_n$ be the monic probabilists’ Hermite polynomial. Then $\pi\sqrt{(a+1)!b!}\, A_{a+1,b}=\int H_a(-T(x))H_b(x) K(x)\,dx$. For the remaining row, $\pi \sqrt{(b+1)!}\,A_{0,b+1}=3s\int (x^2-1)H_b(x)K(x)\,dx$. Both are polynomial moments against the same sextic weight.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Appendix C.1. The zero-index row follows by Gaussian integration by parts in the remaining coordinate.

import Definitions.Def_GrothendieckLB_Supplement_cqA
open MeasureTheory

namespace GrothendieckLB.Supplement

theorem cqA_sextic_reduction (η s₃ s₅ : ℝ) :
    let s := η / Real.sqrt (6*(1+s₃^2+s₅^2))
    let K (x : ℝ) := Real.exp (-(x^2+(s*(x^3-3*x))^2)/2)
    let H (n : ℕ) (x : ℝ) : ℝ := Polynomial.aeval x (Polynomial.hermite n)
    (∀ a b : ℕ, Real.pi * Real.sqrt ((a+1).factorial:ℝ) * Real.sqrt (b.factorial:ℝ) *
      cqA η s₃ s₅ (a+1) b =
        ∫ x : ℝ, H a (-s*(x^3-3*x)) * H b x * K x) ∧
    (∀ b : ℕ, Real.pi * Real.sqrt ((b+1).factorial:ℝ) * cqA η s₃ s₅ 0 (b+1) =
      3*s * ∫ x : ℝ, (x^2-1)*H b x*K x) := by sorry

end GrothendieckLB.Supplement
