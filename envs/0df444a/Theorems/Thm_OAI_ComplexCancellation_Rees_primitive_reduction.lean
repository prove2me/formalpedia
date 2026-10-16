-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Rees_primitive_reduction
-- name    : OAI.ComplexCancellation.Rees.primitive_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:56:11.918998+00:00
-- url     : https://prove2.me/theorems/7cb7ecaa-593f-46dc-bbec-b0bee78b4b9a
-- title:
--   A nonzero locally nilpotent derivation of $B$ killing $q$ yields a nonzero one on the special fibre $B/qB$
-- statement:
--   Let $q,\hat p,\hat s,\hat u,\hat F,\hat J$ be indeterminates and let
--
--   $$
--   B=\mathbb{C}[q,\hat p,\hat s,\hat u,\hat F,\hat J]/(\hat H),\qquad \hat H=\hat x^2\hat F-(1+2\hat s\hat x)\hat J-\hat p^2\hat J^2-q^3\hat p\hat u,\qquad \hat x=\hat s^2+\hat u^3+\hat p^2\hat F .
--   $$
--
--   Let $G=\mathbb{C}[p,s,u,F,J]/\bigl(x^2F-(1+2sx)J-p^2J^2\bigr)$, where $x=s^2+u^3+p^2F$, and let $\operatorname{red}:B\to G$ be the $\mathbb{C}$-algebra homomorphism with $q\mapsto0$ and $\hat p,\hat s,\hat u,\hat F,\hat J\mapsto p,s,u,F,J$. It is surjective with kernel $qB$, so $\operatorname{red}(b)\neq0$ means exactly that $q$ does not divide $b$ in $B$; thus $G$ is the special fibre of $B$ at $q=0$.
--
--   **Theorem.** Let $E$ be a nonzero locally nilpotent $\mathbb{C}$-derivation of $B$ (for every $y\in B$ there is $n\in\mathbb{N}$ with $E^n(y)=0$) such that $E(q)=0$, and let $b\in B$ with $E(b)=0$. Then there is a $\mathbb{C}$-derivation $D$ of $G$ such that
--
--   $$
--   D\ \text{is locally nilpotent},\qquad D\neq0,\qquad D\bigl(\operatorname{red}(b)\bigr)=0 .
--   $$
--
--   A derivation killing $q$ always descends to $B/qB\cong G$, but the induced derivation may be zero if all values of $E$ are divisible by $q$; the content of the theorem is that one can first divide out the largest such power of $q$ while keeping $q$ and $b$ invariant, so that the reduction is nonzero. Together with the preceding transfer from derivations of the hypersurface ring $A=\mathbb{C}[p,s,u,F,J]/(x^2F-(1+2sx)J-p^2J^2-pu)$ to $B$, it produces nonzero locally nilpotent derivations of $G$ with prescribed invariants.
--
--   **Formalization Note** $B$ is `MvPolynomial (Fin 6) ℂ ⧸ (relation)` with `X 0, …, X 5` standing for $q,\hat p,\hat s,\hat u,\hat F,\hat J$; $\operatorname{red}$ is `Rees.red` and $G$ is `Degeneration.G`, with `X 0, …, X 4` standing for $p,s,u,F,J$. Local nilpotence is `LND.LocallyNilpotent`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/ReesDerivation.lean#L108-L140

import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial

theorem OAI.ComplexCancellation.Rees.primitive_reduction (E : Derivation ℂ B B) (hE : LND.LocallyNilpotent E)
    (hEn : E ≠ 0) (hEq : E q=0) (s : B) (hEs : E s=0) :
    ∃ D : Derivation ℂ Degeneration.G Degeneration.G,
      LND.LocallyNilpotent D ∧ D ≠ 0 ∧ D (red s)=0 := by sorry
