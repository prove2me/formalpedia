-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_AffineModification_piece_odd
-- name    : OAI.ComplexCancellation.AffineModification.piece_odd
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:03:28.797176+00:00
-- url     : https://prove2.me/theorems/ae55ed18-15d4-4225-9431-a123833dab07
-- title:
--   Odd-degree elements of $R[\tau,V]/(\tau^2V-v)$ are multiples of $\tau V^{n+1}$
-- statement:
--   Let $R$ be a commutative ring, let $v \in R$, and let $T_v = R[X_0,X_1]/(X_0^2X_1 - v)$. Write $\tau$ and $V$ for the classes of $X_0$ and $X_1$, so that $\tau^2 V = v$ in $T_v$, and identify every $s \in R$ with its image in $T_v$. Give $T_v$ the $\mathbb{Z}$-grading in which $R$ has degree $0$, $\tau$ has degree $-1$ and $V$ has degree $2$: for $e \in \mathbb{Z}$, the homogeneous piece $(T_v)_e$ is the image in $T_v$ of the polynomials that are weighted homogeneous of weight $e$ for the weights $\mathrm{wt}(X_0) = -1$, $\mathrm{wt}(X_1) = 2$. Equivalently, $(T_v)_e$ is the $R$-linear span of the monomials $\tau^a V^b$ with $2b - a = e$. Since the relation $X_0^2X_1 - v$ has weight $0$, this is a grading of $T_v$.
--
--   For every natural number $n$, every homogeneous element of degree $2n+1$ is an $R$-multiple of the monomial $\tau V^{n+1}$:
--
--   $$
--   \forall\, r \in (T_v)_{2n+1}\ \ \exists\, s \in R:\qquad r = \tau\, V^{n+1}\, s .
--   $$
--
--   Since $\tau V^{n+1}$ itself has degree $2(n+1) - 1 = 2n+1$, it follows that $(T_v)_{2n+1} = \tau V^{n+1} R$: each odd positive piece is generated over $R$ by a single monomial. Together with the analogous descriptions of the pieces of negative degree and of even nonnegative degree, this is used to factor a common monomial out of the values of a homogeneous derivation of $T_v$ on the coefficient ring $R$.
--
--   **Formalization Note** No hypothesis is placed on $R$ beyond commutativity, and none on $v$. The piece $(T_v)_e$ is `pieces R v e`, the image of `weightedHomogeneousSubmodule R weight e` (with `weight = ![-1, 2]`) under the quotient map `π R v`, and the scalar $s$ enters through `algebraMap R (T R v)`. The degree is the integer `2 * (n : ℤ) + 1` with $n$ a natural number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/ModificationGrading.lean#L87-L105

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

theorem OAI.ComplexCancellation.AffineModification.piece_odd (n : ℕ) {r : T R v} (hr : r ∈ pieces R v (2*(n:ℤ)+1)) :
    ∃ s : R, r=τ R v*V R v^(n+1)*algebraMap R (T R v) s := by sorry
