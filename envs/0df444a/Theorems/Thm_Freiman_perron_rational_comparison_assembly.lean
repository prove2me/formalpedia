-- Prove2me | Theorems.Thm_Freiman_perron_rational_comparison_assembly
-- name    : Freiman.perron_rational_comparison_assembly
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:29.218295+00:00
-- url     : https://prove2.me/theorems/0d6ccecd-dd8d-433d-804d-fad83ec172c2
-- title:
--   Reduced and unreduced rational comparison in the Perron proof
-- statement:
--   This is the final rational-case argument after its classical inputs are supplied explicitly: choose the nearest numerator, reduce p/q=p′/q′, use escape of q′ to obtain a fraction in (0,1) beyond every early convergent, and split by Legendre. A nonconvergent has inverse error at most two. A convergent has inverse error P_n, multiplied by 1/d² for q=dq′. These two scalar cases are the remaining open obligation.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, final two paragraphs of found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem perron_rational_comparison_assembly (b : ℕ → ℕ+)
    (hirr : Irrational (cfValue b)) (h0 : 0 < cfValue b) (h1 : cfValue b < 1)
    (hnearest : ∀ q : ℕ, integerDistance ((q:ℝ)*cfValue b)=|(q:ℝ)*cfValue b-(nearestNumerator (cfValue b) q:ℝ)|)
    (hescape : ∀ R : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q≤q → R≤reducedApproximationDenominator (cfValue b) q)
    (hlegendre : ∀ p q : ℕ, 0<p → p<q → 2≤q → Nat.Coprime p q →
      |cfValue b-(p:ℝ)/q|<1/(2*(q:ℝ)^2) → ∃ n : ℕ, cfConvergent b n=(p:ℝ)/q)
    (hconv : ∀ n : ℕ, cfConvergent b n=(continuantP b n:ℝ)/continuantQ b n)
    (hcop : ∀ n : ℕ, Nat.Coprime (continuantP b n) (continuantQ b n))
    (herror : ∀ n : ℕ, 1/((continuantQ b n:ℝ)*|(continuantQ b n:ℝ)*cfValue b-(continuantP b n:ℝ)|)=perronValue b n) :
    ∀ K : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      approximationValue (cfValue b) (q + 1) ≤ 2 ∨
      ∃ n : ℕ, K ≤ n ∧ approximationValue (cfValue b) (q + 1) ≤ perronValue b n := by
  sorry

end Freiman
