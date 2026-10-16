-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_AffineModification_derivation_zero_of_generators
-- name    : OAI.ComplexCancellation.AffineModification.derivation_zero_of_generators
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:11:36.989279+00:00
-- url     : https://prove2.me/theorems/de179fcc-2972-4eb6-ac0d-a9dbe232091e
-- title:
--   A derivation of $R[\tau,V]/(\tau^2V-v)$ vanishing on $R$, $\tau$ and $V$ is zero
-- statement:
--   Let $k$ be a field, $R$ a commutative $k$-algebra and $v \in R$. Let $T_v = R[X_0,X_1]/(X_0^2X_1 - v)$, and write $\tau$ and $V$ for the classes of $X_0$ and $X_1$, so that $\tau^2 V = v$. Regard $T_v$ as a $k$-algebra through $k \to R \to T_v$, and for $r \in R$ write $\bar r$ for its image in $T_v$. Let $D : T_v \to T_v$ be a $k$-linear derivation.
--
--   If $D$ annihilates all coefficients and both generators, then $D$ is identically zero:
--
--   $$
--   \Big(\forall\, r \in R:\ D(\bar r) = 0\Big)\ \wedge\ D(\tau) = 0\ \wedge\ D(V) = 0 \quad\Longrightarrow\quad D = 0 .
--   $$
--
--   This is the uniqueness principle for derivations of $T_v$, which is generated as an algebra by $\tau$ and $V$ over the image of $R$: two derivations of $T_v$ that agree on $R$, on $\tau$ and on $V$ coincide (apply the statement to their difference). It is used to recognise that a derivation vanishes, or equals another one, by checking it on these generators only.
--
--   **Formalization Note** Only the field structure of $k$ is used: the characteristic-zero hypothesis on $k$ and the domain hypothesis on $R$ that are in force in the surrounding Lean section are omitted, and there is no hypothesis on $v$. The map $r \mapsto \bar r$ is `coefficientHom v`, the structure map $R \to T_v$ as a $k$-algebra homomorphism.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Extraction.lean#L78-L94

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
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.AffineModification
open MvPolynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
variable (v : R) (hv : v ≠ 0)

omit [CharZero k] [IsDomain R] in
theorem OAI.ComplexCancellation.AffineModification.derivation_zero_of_generators (D : Derivation k (T R v) (T R v))
    (hc : ∀ r, D (coefficientHom (k := k) v r)=0)
    (hτ : D (τ R v)=0) (hV : D (V R v)=0) : D=0 := by sorry
