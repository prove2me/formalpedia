-- Prove2me | Theorems.Thm_JakulinBratko_eq3_mutual_information
-- name    : JakulinBratko.eq3_mutual_information
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:17.619801+00:00
-- url     : https://prove2.me/theorems/dd54f11b-2104-45bd-a3a4-6207f49f03c4
-- title:
--   Eq. (3) — forms of the mutual information; nonnegative; zero iff independent
-- statement:
--   Let $P$ be a joint law. For disjoint sets $R,Y$ of attributes,
--
--   $$
--   I(R;Y)=H(R)+H(Y)-H(R\cup Y)=H(R)-H(R\mid Y)=I(Y;R)=H(Y)-H(Y\mid R),
--   $$
--
--   where $I(R;Y)$ and $H(R\mid Y)$ are the defining sums. Moreover:
--
--   1. $I(R;Y)\ge 0$;
--   2. $I(R;Y)=0$ if and only if $P(z)=P(z|_R)\,P(z|_Y)$ for every assignment $z$ of $R\cup Y$;
--   3. for distinct attributes $A,B$, the interaction information of Eq. (10) satisfies $I(\{A,B\})=I(\{A\};\{B\})$.
--
--   This is the $2$-way case of the mission's goal: both directions of the independence criterion, including at points of zero mass.
--
--   Differences from the source:
--   - generalization: single attributes A, B → disjoint Finsets R, Y of attributes; reason: the paper itself uses groups (I(A, B; C) in Eq. (5)); singletons give the printed display
--   - reading: I(A; B) of Eq. (3) and the k = 2 case of Eq. (10) carry one symbol → the equality of miSum and I P {A, B} is stated as a clause; reason: the paper identifies them by notation; the mission keeps them as separate definitions
--   - encoding: P(a, b) = P(a)P(b) → equality of marg at every assignment z of R ∪ Y, with restrictions by Finset.restrict₂; reason: Lean convention; same instances
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.2, Eq. (3) and the sentences after it, p.4

import Definitions.Def_JakulinBratko_IsLaw
import Definitions.Def_JakulinBratko_I
import Definitions.Def_JakulinBratko_condEntSum
import Definitions.Def_JakulinBratko_miSum

namespace JakulinBratko

/-- Eq. (3), p.4, and the sentences after it (Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3), for disjoint groups of attributes: the forms
of the mutual information, its nonnegativity, its vanishing exactly under independence, and its
agreement with the two-attribute case of the interaction information of Eq. (10). -/
theorem eq3_mutual_information {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (hP : IsLaw P) :
    (∀ R Y : Finset ι, Disjoint R Y →
      miSum P R Y = H P R + H P Y - H P (R ∪ Y) ∧
      miSum P R Y = H P R - condEntSum P R Y ∧
      miSum P R Y = miSum P Y R ∧
      miSum P R Y = H P Y - condEntSum P Y R ∧
      0 ≤ miSum P R Y ∧
      (miSum P R Y = 0 ↔ ∀ z : (∀ i : ↥(R ∪ Y), α i),
        marg P (R ∪ Y) z =
          marg P R (Finset.restrict₂ Finset.subset_union_left z) *
            marg P Y (Finset.restrict₂ Finset.subset_union_right z))) ∧
    ∀ A B : ι, A ≠ B → I P {A, B} = miSum P {A} {B} := by sorry

end JakulinBratko
