-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_AffineModification_piece_negative
-- name    : OAI.ComplexCancellation.AffineModification.piece_negative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:01:16.636289+00:00
-- url     : https://prove2.me/theorems/37256855-8469-42ee-a740-070f2d9df2df
-- title:
--   Elements of weight $-n$ in $R[\tau,V]/(\tau^2V-v)$ are the multiples $\tau^n s$ with $s\in R$
-- statement:
--   Let $R$ be a commutative ring (not necessarily a domain) and $v\in R$. Consider the $R$-algebra
--
--   $$
--   T_v=R[\tau,V]/(\tau^2V-v),
--   $$
--
--   graded by giving $\tau$ weight $-1$, $V$ weight $2$ and the elements of $R$ weight $0$. The relation $\tau^2V-v$ is weighted homogeneous of weight $0$, so the images $T_{v,e}$ in $T_v$ of the weighted-homogeneous polynomials of weight $e$ form a $\mathbb{Z}$-grading $T_v=\bigoplus_{e\in\mathbb{Z}}T_{v,e}$. Elements $s\in R$ are regarded as elements of $T_v$ through the structure map.
--
--   **Theorem.** Let $n\in\mathbb{N}$. Every element of weight $-n$ is $\tau^n$ times an element of $R$:
--
--   $$
--   r\in T_{v,-n}\ \Longrightarrow\ \exists\,s\in R:\ \ r=\tau^n\,s .
--   $$
--
--   For $n=0$ this says that the weight-$0$ part of $T_v$ is the image of $R$. Together with the analogous descriptions of the pieces of weight $2n$ (multiples of $V^n$) and $2n+1$ (multiples of $\tau V^{n+1}$), it shows that each graded piece of $T_v$ is generated over $R$ by a single monomial. This is used to see, for example, that a homogeneous element not divisible by $\tau$ has even nonnegative weight, in the analysis of locally nilpotent derivations of such modifications.
--
--   **Formalization Note** $T_v$ is `AffineModification.T R v`, the quotient of `MvPolynomial (Fin 2) R` by `X 0 ^ 2 * X 1 - C v`; $\tau$ and $V$ are `τ R v` and `V R v`, the grading is `pieces R v` (the image of `weightedHomogeneousSubmodule R ![-1, 2]`), and $s\in R$ enters as `algebraMap R (T R v) s`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/ModificationGrading.lean#L51-L67

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
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] (v : R)
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem OAI.ComplexCancellation.AffineModification.piece_negative (n : ℕ) {r : T R v} (hr : r ∈ pieces R v (-(n:ℤ))) :
    ∃ s : R, r=τ R v^n*algebraMap R (T R v) s := by sorry
