-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_RationalSlice_constant_fraction
-- name    : OAI.ComplexCancellation.RationalSlice.constant_fraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:00:33.17403+00:00
-- url     : https://prove2.me/theorems/2db0699b-a837-40d9-bfde-32fa908aa2c1
-- title:
--   Constants of the extension of a locally nilpotent derivation to the fraction field are quotients of kernel elements
-- statement:
--   Let $k$ be a field, let $R$ be a commutative $k$-algebra that is an integral domain, and let $K$ be the field of fractions of $R$, with the compatible $k$-algebra structure ($k\to R\to K$). Every $k$-derivation $D$ of $R$ extends uniquely to a $k$-derivation $\tilde D$ of $K$, given by the quotient rule $\tilde D(a/b)=\bigl(D(a)\,b-a\,D(b)\bigr)/b^2$.
--
--   **Theorem.** Let $D$ be a locally nilpotent $k$-derivation of $R$, i.e. for every $r\in R$ there is $n\in\mathbb{N}$ with $D^n(r)=0$. If $\gamma\in K$ satisfies $\tilde D(\gamma)=0$, then there are $a,b\in R$ with
--
--   $$
--   D(a)=0,\qquad D(b)=0,\qquad b\neq0,\qquad \gamma=\frac{a}{b}\ \text{ in } K .
--   $$
--
--   Together with the obvious converse (a quotient of two elements of $\ker D$ is killed by $\tilde D$), this identifies the field of constants of $\tilde D$ with the field of fractions of $\ker D$ inside $K$. In the cancellation argument it is used to clear constants of $\tilde D$ by nonzero elements of $\ker D$, when a ring with a locally nilpotent derivation is compared with a polynomial ring over the field of constants.
--
--   **Formalization Note** $\tilde D$ is `FractionDerivation.extend D`, constructed by lifting $r\mapsto r+D(r)\varepsilon$ into the dual numbers over $K$. The characteristic-zero assumptions of the surrounding file are omitted for this statement, so $k$ may have any characteristic.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/RationalSlice.lean#L62-L77

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

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.RationalSlice
open DifferentialSlice FractionDerivation
variable {k R K : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [Algebra k R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Algebra k K] [IsScalarTower k R K]

omit [CharZero k] [CharZero K] in
theorem OAI.ComplexCancellation.RationalSlice.constant_fraction (D : Derivation k R R) (hD : LND.LocallyNilpotent D)
    {c : K} (hc : extend D c = 0) :
    ∃ a b : R, D a = 0 ∧ D b = 0 ∧ b ≠ 0 ∧ algebraMap R K a / algebraMap R K b = c := by sorry
