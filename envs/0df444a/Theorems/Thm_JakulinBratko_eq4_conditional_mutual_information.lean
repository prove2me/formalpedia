-- Prove2me | Theorems.Thm_JakulinBratko_eq4_conditional_mutual_information
-- name    : JakulinBratko.eq4_conditional_mutual_information
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:57.575208+00:00
-- url     : https://prove2.me/theorems/593e2a82-73f2-42ed-9bce-79fb58221632
-- title:
--   Eq. (4) — forms of the conditional mutual information; nonnegative; the average over the values of $C$
-- statement:
--   Let $P$ be a joint law. For pairwise disjoint sets $R,Y,Z$ of attributes,
--
--   $$
--   I(R;Y\mid Z)=H(R\mid Z)+H(Y\mid Z)-H(R\cup Y\mid Z)=H(R\mid Z)-H(R\mid Y\cup Z)
--   =H(R\cup Z)+H(Y\cup Z)-H(Z)-H(R\cup Y\cup Z),
--   $$
--
--   where the left side and the conditional entropies are the defining sums, and $I(R;Y\mid Z)\ge 0$.
--
--   For distinct attributes $A,B,D$, the sum $I(\{A\};\{B\}\mid\{D\})$ is the average over the values of $D$ of the mutual information of $A$ and $B$ under the conditional law:
--
--   $$
--   I(\{A\};\{B\}\mid\{D\})=I(\{A,B\}\mid D).
--   $$
--
--   The nonnegativity is what makes clause (c) of the goal work by induction on the number of attributes, and the last identity ties the sum of Eq. (4) to the conditional interaction information of Eq. (10).
--
--   **Formalization Note** The paper's attribute $C$ is written $D$ here, because `C` is the total correlation.
--
--   Differences from the source:
--   - generalization: single attributes A, B, C → pairwise disjoint Finsets R, Y, Z for the forms and the sign; distinct attributes for the average; reason: the paper itself uses groups (H(A|B, C), H(AB|C)); singletons give the printed display
--   - reading: "the expected 2-way informative conditional interaction information ... over the values of C" → condI P D {A, B}, the average of I under condLaw weighted by attrMarg; reason: the sentence is the only definition the paper gives; this is its literal content
--   - encoding: P(a, b|c) / (P(a|c)P(b|c)) → the quotient with conditional probabilities cleared, P(z)P(z|_Z) / (P(z|_(R∪Z)) P(z|_(Y∪Z))); reason: Lean convention; the two agree wherever P(z) > 0 and all other terms have weight 0
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.3, Eq. (4), p.4; sign, p.5; expectation, §2.3.2, p.7

import Definitions.Def_JakulinBratko_IsLaw
import Definitions.Def_JakulinBratko_H
import Definitions.Def_JakulinBratko_condI
import Definitions.Def_JakulinBratko_condEntSum
import Definitions.Def_JakulinBratko_cmiSum

namespace JakulinBratko

/-- Eq. (4), p.4, the sentence on p.5 and the sentence on p.7 (Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3), for pairwise disjoint groups of
attributes: the forms of the conditional mutual information, its nonnegativity, and, for three
distinct attributes, its reading as the average over the values of the conditioning attribute. -/
theorem eq4_conditional_mutual_information {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (hP : IsLaw P) :
    (∀ R Y Z : Finset ι, Disjoint R Y → Disjoint R Z → Disjoint Y Z →
      cmiSum P R Y Z = condEntSum P R Z + condEntSum P Y Z - condEntSum P (R ∪ Y) Z ∧
      cmiSum P R Y Z = condEntSum P R Z - condEntSum P R (Y ∪ Z) ∧
      cmiSum P R Y Z = H P (R ∪ Z) + H P (Y ∪ Z) - H P Z - H P (R ∪ Y ∪ Z) ∧
      0 ≤ cmiSum P R Y Z) ∧
    ∀ A B D : ι, A ≠ B → A ≠ D → B ≠ D →
      cmiSum P {A} {B} {D} = condI P D {A, B} := by sorry

end JakulinBratko
