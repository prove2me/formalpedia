-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_LaurentDerivation_locallyNilpotent
-- name    : OAI.ComplexCancellation.LaurentDerivation.locallyNilpotent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:47:24.636076+00:00
-- url     : https://prove2.me/theorems/a44ba0b6-6b87-42af-a1a3-3191511e9b02
-- title:
--   The coefficientwise extension of a locally nilpotent derivation to Laurent polynomials is locally nilpotent
-- statement:
--   Let $k$ and $R$ be commutative rings with $R$ a $k$-algebra, and let $D$ be a $k$-derivation of $R$ that is locally nilpotent: for every $r\in R$ there is $n\in\mathbb{N}$ with $D^n(r)=0$. Let $\hat D$ be the coefficientwise extension of $D$ to the Laurent polynomial ring $R[T,T^{-1}]$,
--   $$\hat D\Bigl(\sum_{m\in\mathbb{Z}}r_mT^m\Bigr)=\sum_{m\in\mathbb{Z}}D(r_m)\,T^m,$$
--   which is a $k$-derivation of $R[T,T^{-1}]$ with $\hat D(T^m)=0$. Then $\hat D$ is locally nilpotent:
--
--   $$\forall\, g\in R[T,T^{-1}]\ \ \exists\, n\in\mathbb{N}:\qquad \hat D^{\,n}(g)=0 .$$
--
--   The variable $T$ is invariant under $\hat D$. The statement allows a locally nilpotent derivation of a coefficient ring $P$ to be used on the Laurent ring $P[T,T^{-1}]$, which is the target of the forward map attached to a frame in the construction.
--
--   **Formalization Note** $\hat D$ is `LaurentDerivation.extension D`, built by applying $D$ to the coefficient function (`Finsupp.mapRange`); the hypothesis and conclusion are written with function iterates `(D : R → R)^[n]` rather than with `LND.LocallyNilpotent`, and $k$ is only assumed to be a commutative ring.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/LaurentDerivation.lean#L46-L66

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

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.LaurentDerivation
open LaurentPolynomial
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem OAI.ComplexCancellation.LaurentDerivation.locallyNilpotent (D : Derivation k R R)
    (hD : ∀ r : R, ∃ n, (D : R → R)^[n] r=0) :
    ∀ p : LaurentPolynomial R, ∃ n,
      (extension D : LaurentPolynomial R → LaurentPolynomial R)^[n] p=0 := by sorry
