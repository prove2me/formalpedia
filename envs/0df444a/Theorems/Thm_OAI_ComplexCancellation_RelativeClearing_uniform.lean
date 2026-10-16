-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_RelativeClearing_uniform
-- name    : OAI.ComplexCancellation.RelativeClearing.uniform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:57:51.524668+00:00
-- url     : https://prove2.me/theorems/df78ec3f-8efc-439a-a697-4901e7266fe5
-- title:
--   A common nonzero invariant denominator for the derivatives of finitely many elements
-- statement:
--   Let $k$ be a commutative ring, let $A$ be a commutative $k$-algebra that is an integral domain, let $B$ and $R$ be commutative $k$-algebras, and let $h:A\to B$ and $f:B\to R$ be $k$-algebra homomorphisms. Let $D$ be a $k$-derivation of $A$. Call an element $y\in R$ clearable if there exist $c\in A$ and $t\in B$ with
--
--   $$
--   D(c)=0,\qquad c\neq0,\qquad f(h(c))\,y=f(t),
--   $$
--
--   that is, $y$ lands in $f(B)$ after multiplication by the image of a nonzero $D$-invariant element of $A$. The clearable elements form a $k$-subalgebra of $R$.
--
--   **Theorem.** Let $E$ be a $k$-derivation of $R$ such that $E(f(b))$ is clearable for every $b\in B$, and let $S\subseteq B$ be a finite set. Then a single invariant clears all the elements $E(f(b))$ with $b\in S$:
--
--   $$
--   \exists\,c\in A:\qquad D(c)=0,\quad c\neq0,\quad \forall\,b\in S\ \ \exists\,t\in B:\ \ f(h(c))\,E(f(b))=f(t).
--   $$
--
--   Applied to a finite generating set $S$ of $B$, this yields one nonzero invariant $c$ such that the scaled derivation $f(h(c))\,E$ maps $f(B)$ into itself on generators, which is the first step in restricting a derivation of a larger ring $R$ to a derivation of $B$ after multiplying by an invariant. It is the relative, invariant version of clearing denominators.
--
--   **Formalization Note** The clearable elements form `RelativeClearing.subalgebra h f D`, and the finite set is a `Finset B`. The hypothesis is required for every $b\in B$, although only the elements of $S$ are used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/RelativeClearing.lean#L29-L49

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
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.RelativeClearing
variable {k A B R : Type*} [CommRing k] [CommRing A] [IsDomain A] [CommRing B] [CommRing R]
  [Algebra k A] [Algebra k B] [Algebra k R]
variable (h : A →ₐ[k] B) (f : B →ₐ[k] R) (D : Derivation k A A)

theorem OAI.ComplexCancellation.RelativeClearing.uniform (s : Finset B) (E : Derivation k R R)
    (hc : ∀ b, E (f b) ∈ subalgebra h f D) :
    ∃ c : A, D c=0 ∧ c≠0 ∧ ∀ b∈s, ∃ t : B, f (h c)*E (f b)=f t := by sorry
