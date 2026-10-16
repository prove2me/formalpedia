-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Rees_clear_order
-- name    : OAI.ComplexCancellation.Rees.clear_order
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:54:08.786208+00:00
-- url     : https://prove2.me/theorems/8883ce94-d8eb-432b-8384-d3ccb6bf983c
-- title:
--   Every nonzero Laurent polynomial over $A$ is, up to a power of $T$, the image of an element of $B$ not divisible by $q$
-- statement:
--   Let $P=\mathbb{C}[p,s,u,F,J]$, $x=s^2+u^3+p^2F$, $H=x^2F-(1+2sx)J-p^2J^2-pu$, and $A=P/(H)$. Let $L=A[T,T^{-1}]$ be the ring of Laurent polynomials over $A$, which contains $A$ as the constants. Let
--
--   $$
--   B=\mathbb{C}[q,\hat p,\hat s,\hat u,\hat F,\hat J]/(\hat H),\qquad \hat H=\hat x^2\hat F-(1+2\hat s\hat x)\hat J-\hat p^2\hat J^2-q^3\hat p\hat u,\qquad \hat x=\hat s^2+\hat u^3+\hat p^2\hat F .
--   $$
--
--   Let $\iota:B\to L$ be the $\mathbb{C}$-algebra homomorphism with
--
--   $$
--   q\mapsto T,\quad \hat p\mapsto pT^{-1},\quad \hat s\mapsto s,\quad \hat u\mapsto u,\quad \hat F\mapsto FT^2,\quad \hat J\mapsto JT^2
--   $$
--
--   (it is well defined because $\hat H\mapsto T^2H=0$, and it is injective). Let $G=\mathbb{C}[p,s,u,F,J]/\bigl(x^2F-(1+2sx)J-p^2J^2\bigr)$, with $x=s^2+u^3+p^2F$ as before, and let $\operatorname{red}:B\to G$ be the $\mathbb{C}$-algebra homomorphism with $q\mapsto0$ and $\hat p,\hat s,\hat u,\hat F,\hat J\mapsto p,s,u,F,J$. It is surjective with kernel $qB$, so $\operatorname{red}(b)\neq0$ means exactly that $q$ does not divide $b$ in $B$; thus $G$ is the special fibre of $B$ at $q=0$.
--
--   **Theorem.** For every nonzero $r\in L$ there exist an integer $i$ and an element $b\in B$ such that
--
--   $$
--   \operatorname{red}(b)\neq0\qquad\text{and}\qquad \iota(b)=T^{i}\,r .
--   $$
--
--   So every nonzero Laurent polynomial over $A$ becomes, after multiplication by a suitable (possibly negative) power of $T$, the image of an element of $B$ that is not divisible by $q$. For a constant $r\in A$, the exponent $i$ and the nonzero element $\operatorname{red}(b)$ of the special fibre $G$ record how $r$ degenerates; this is how elements of $A$ are transported to $G$ in the argument showing that $A$ is not a polynomial ring.
--
--   **Formalization Note** $B$ is `MvPolynomial (Fin 6) ℂ ⧸ (relation)` with `X 0, …, X 5` standing for $q,\hat p,\hat s,\hat u,\hat F,\hat J$; $A$ is `P ⧸ (H)` with `X 0, …, X 4` standing for $p,s,u,F,J$; $L$ is `LaurentPolynomial A` and $T^i$ is `T i`; $\iota$ is `Rees.embedding`; $\operatorname{red}$ is `Rees.red` and $G$ is `Degeneration.G`, whose variables are ordered in the same way as those of $A$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/ReesClearing.lean#L61-L77

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

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial

theorem OAI.ComplexCancellation.Rees.clear_order (r : L) (hr : r ≠ 0) :
    ∃ (i : ℤ) (s : B), red s ≠ 0 ∧ embedding s=T i*r := by sorry
