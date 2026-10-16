-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_AffineModification_extract
-- name    : OAI.ComplexCancellation.AffineModification.extract
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:13:40.198277+00:00
-- url     : https://prove2.me/theorems/8e2abede-b48d-4823-8721-faadeed4ae5e
-- title:
--   Extracting a semi-invariant locally nilpotent derivation of $R$ from a homogeneous one of $R[\tau,V]/(\tau^2V-v)$
-- statement:
--   Let $k$ be a field of characteristic zero, let $R$ be an integral domain that is a $k$-algebra, and fix $v \in R$ with $v \neq 0$. Let $T_v = R[X_0,X_1]/(X_0^2X_1 - v)$, write $\tau, V$ for the classes of $X_0, X_1$ (so $\tau^2V = v$), and identify $R$ with its image in $T_v$. Grade $T_v$ by $\mathbb{Z}$ with $R$ in degree $0$, $\deg\tau = -1$ and $\deg V = 2$: the homogeneous piece $(T_v)_e$ is the $R$-span of the monomials $\tau^aV^b$ with $2b - a = e$ (the image of the weighted homogeneous polynomials of weight $e$). A derivation $D$ is called locally nilpotent if for every element $z$ there is $m \in \mathbb{N}$ with $D^m(z) = 0$.
--
--   Let $H$ be a $k$-derivation of $R$ with $H(v) = 2v$, and let $\hat H$ be the $k$-derivation of $T_v$ that acts as $H$ on $R$ and satisfies $\hat H(\tau) = 0$ and $\hat H(V) = 2V$ (it is well defined because it maps $\tau^2V - v$ to $2(\tau^2V - v)$). Let $D$ be a $k$-derivation of $T_v$ such that
--
--   1. $D$ is locally nilpotent and $D \neq 0$;
--   2. $D$ is homogeneous of some degree $j \in \mathbb{Z}$, that is, $D\big((T_v)_e\big) \subseteq (T_v)_{e+j}$ for every $e \in \mathbb{Z}$;
--   3. $D$ commutes with $\hat H$: $\hat H(D(z)) = D(\hat H(z))$ for all $z \in T_v$;
--   4. $D(V) = 0$.
--
--   Then there exist a $k$-derivation $E$ of $R$ and a natural number $n$ such that $E \neq 0$, $E$ is locally nilpotent, and
--
--   $$
--   H(E(r)) - E(H(r)) = -\,n\,E(r)\quad\text{for all } r \in R, \qquad\qquad E(E(v)) = 0 .
--   $$
--
--   Thus a homogeneous, $\hat H$-equivariant locally nilpotent derivation of $T_v$ that kills $V$ forces a nonzero locally nilpotent derivation of the coefficient ring $R$ which is an eigenvector of $\operatorname{ad} H$ with nonpositive eigenvalue $-n$ and satisfies $E^2(v) = 0$; no invariance of $R$ under $D$ is assumed. In the proof that the hypersurface ring $A = \mathbb{C}[p,s,u,F,J]/\big(x^2F - (1+2sx)J - p^2J^2 - pu\big)$ with $x = s^2 + u^3 + p^2F$ is not a polynomial ring in four variables, this is applied with $R = \mathbb{C}[a,b,c,d,u]/(ac - bd - 1)$, $v = a^3b - a^2u^3 - d^2$ and $H$ the Euler derivation with weights $1, -1, -1, 1, 0$ on $a, b, c, d, u$, where a separate rigidity result shows that no such $E$ can exist.
--
--   **Formalization Note** Local nilpotence is `LND.LocallyNilpotent`; the pieces are `pieces R v e`; $\hat H$ is `euler v H hH`, induced on the quotient by the derivation of $R[X_0,X_1]$ acting as $H$ on coefficients with $X_0 \mapsto 0$ and $X_1 \mapsto 2X_1$; homogeneity of $D$ is the hypothesis `hshift`. The term $n\,E(r)$ is the natural-number multiple `n • E r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/HomogeneousExtraction.lean#L62-L116

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
include hv

theorem OAI.ComplexCancellation.AffineModification.extract (H : Derivation k R R) (hH : H v=2*v)
    (D : Derivation k (T R v) (T R v)) (hD : LND.LocallyNilpotent D) (hDn : D ≠ 0)
    (j : ℤ) (hshift : ∀ e r, r ∈ pieces R v e → D r ∈ pieces R v (e+j))
    (hcomm : ∀ z, euler v H hH (D z)=D (euler v H hH z))
    (hV : D (V R v)=0) :
    ∃ (E : Derivation k R R) (n : ℕ), E ≠ 0 ∧ LND.LocallyNilpotent E ∧
      (∀ r, H (E r)-E (H r)=-(n • E r)) ∧ E (E v)=0 := by sorry
