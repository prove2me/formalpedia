-- Prove2me | Theorems.Thm_JakulinBratko_eq6_total_correlation_three
-- name    : JakulinBratko.eq6_total_correlation_three
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:17.070672+00:00
-- url     : https://prove2.me/theorems/197bcc45-611c-4414-bbb4-3ceb12ccdd20
-- title:
--   Eq. (6) — total correlation of three attributes; nonnegative; zero iff independent
-- statement:
--   Let $P$ be a joint law and $A,B,D$ distinct attributes (the paper's $A,B,C$). Then
--
--   $$
--   C(\{A,B,D\})=I(A;B)+I(B;D)+I(A;D)+I(\{A,B,D\}).
--   $$
--
--   Moreover $C(\{A,B,D\})\ge 0$, and $C(\{A,B,D\})=0$ if and only if
--
--   $$
--   P(a,b,d)=P(a)\,P(b)\,P(d)
--   $$
--
--   at every assignment of the three attributes, including points of zero mass.
--
--   This is the case of the goal that the paper states explicitly.
--
--   Differences from the source:
--   - encoding: P(A, B, C) = P(A)P(B)P(C) → equality of marg P {A, B, D} s and the product of attrMarg at every assignment s; reason: Lean convention; same instances; the letter C of the page is D
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.3, Eq. (6), p.5, and the sentence after it, p.6

import Definitions.Def_JakulinBratko_IsLaw
import Definitions.Def_JakulinBratko_I
import Definitions.Def_JakulinBratko_C
import Definitions.Def_JakulinBratko_attrMarg
import Definitions.Def_JakulinBratko_miSum

namespace JakulinBratko

/-- Eq. (6), p.5, and the sentence after it, p.6 (Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): for three distinct attributes `A, B, D`
(the paper's `A, B, C`), the total correlation is the sum of the three mutual informations and the
interaction information; it is nonnegative, and zero exactly when `P(A, B, C) = P(A) P(B) P(C)`. -/
theorem eq6_total_correlation_three {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (hP : IsLaw P)
    (A B D : ι) (hAB : A ≠ B) (hAD : A ≠ D) (hBD : B ≠ D) :
    C P {A, B, D} = miSum P {A} {B} + miSum P {B} {D} + miSum P {A} {D} + I P {A, B, D} ∧
    0 ≤ C P {A, B, D} ∧
    (C P {A, B, D} = 0 ↔ ∀ s : (∀ i : ↥({A, B, D} : Finset ι), α i),
      marg P {A, B, D} s =
        attrMarg P A (s ⟨A, by simp⟩) * attrMarg P B (s ⟨B, by simp⟩) *
          attrMarg P D (s ⟨D, by simp⟩)) := by sorry

end JakulinBratko
