-- Prove2me | Theorems.Thm_JakulinBratko_eq5_three_way
-- name    : JakulinBratko.eq5_three_way
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:15.555935+00:00
-- url     : https://prove2.me/theorems/11592622-8f01-4437-9e11-f0bc389d8366
-- title:
--   Eq. (5) — the forms and the symmetry of $I(A;B;C)$
-- statement:
--   Let $P$ be a joint law and $A,B,D$ distinct attributes (the paper's $A,B,C$). The interaction information $I(\{A,B,D\})$ of Eq. (10) satisfies
--
--   $$
--   I(\{A,B,D\})=I(A;B\mid D)-I(A;B)=I(A,B;D)-I(A;D)-I(B;D)
--   $$
--   $$
--   =H(AB)+H(BD)+H(AD)-H(A)-H(B)-H(D)-H(ABD).
--   $$
--
--   Moreover the first form does not depend on which attribute is singled out:
--
--   $$
--   I(A;B\mid D)-I(A;B)=I(A;D\mid B)-I(A;D)=I(D;B\mid A)-I(D;B).
--   $$
--
--   This is the paper's symmetry $I(A;B;C)=I(A;C;B)=I(C;B;A)$. The last two equalities carry its content, because $\{A,B,D\}$ as a set does not record an order.
--
--   Differences from the source:
--   - encoding: I(A; B; C) as a function of an ordered triple → I P {A, B, D} of a Finset, with the symmetry stated as equalities of the first form under permutation; reason: a Finset has no order, so the symmetry of the display is stated on the sum forms; the letter C of the page is D
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.3, Eq. (5) and the sentences after it, p.5

import Definitions.Def_JakulinBratko_IsLaw
import Definitions.Def_JakulinBratko_I
import Definitions.Def_JakulinBratko_miSum
import Definitions.Def_JakulinBratko_cmiSum

namespace JakulinBratko

/-- Eq. (5), p.5, and the symmetry sentence after it (Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): for three distinct attributes
`A, B, D` (the paper's `A, B, C`) the interaction information of Eq. (10) has the printed forms, and the
form `I(A; B | C) - I(A; B)` does not depend on which attribute is singled out. -/
theorem eq5_three_way {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (hP : IsLaw P)
    (A B D : ι) (hAB : A ≠ B) (hAD : A ≠ D) (hBD : B ≠ D) :
    I P {A, B, D} = cmiSum P {A} {B} {D} - miSum P {A} {B} ∧
    I P {A, B, D} = miSum P {A, B} {D} - miSum P {A} {D} - miSum P {B} {D} ∧
    I P {A, B, D} = H P {A, B} + H P {B, D} + H P {A, D}
        - H P {A} - H P {B} - H P {D} - H P {A, B, D} ∧
    cmiSum P {A} {B} {D} - miSum P {A} {B} =
      cmiSum P {A} {D} {B} - miSum P {A} {D} ∧
    cmiSum P {A} {B} {D} - miSum P {A} {B} =
      cmiSum P {D} {B} {A} - miSum P {D} {B} := by sorry

end JakulinBratko
