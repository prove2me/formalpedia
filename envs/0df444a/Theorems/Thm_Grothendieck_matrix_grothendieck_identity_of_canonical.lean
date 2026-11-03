-- Prove2me | Theorems.Thm_Grothendieck_matrix_grothendieck_identity_of_canonical
-- name    : Grothendieck.matrix_grothendieck_identity_of_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:28:25.749418+00:00
-- url     : https://prove2.me/theorems/57ae64f3-11f2-4efa-bf9b-eecb66e345da
-- title:
--   Lemma 2.1 reduced to one scalar bivariate-Gaussian identity
-- statement:
--   Lemma 2.1 of the paper computes the rounding expectation
--
--   $$
--   \mathbb E\Big[\frac{Zu}{\lVert Zu\rVert}\cdot\frac{Zv}{\lVert Zv\rVert}\Big]
--   $$
--
--   for an $r\times n$ Gaussian matrix $Z$ and unit vectors $u,v\in\mathbb R^n$. This node reduces that identity, **including the endpoint case $|u\cdot v|=1$**, to one scalar statement.
--
--   Because the two columns $X=Zu$ and $Y=Zv$ are linear images of $Z$, the $r$ rows of the pair $(X,Y)$ are independent and each row is a two-dimensional Gaussian with covariance $\big(\begin{smallmatrix}1&t\\t&1\end{smallmatrix}\big)$, where $t=u\cdot v$; that law is `reducedLaw r t` and the integrand, the cosine of the angle between the two columns, is `reducedIntegrand`. The hypothesis of this node says precisely that the integral of that integrand against that law is the paper's series $E_r(t)$:
--
--   $$
--   \int W\,\cos\angle\big(W_0,W_1\big)\;d(\text{law of } r \text{ independent } N\big(0,\big(\begin{smallmatrix}1&t\\t&1\end{smallmatrix}\big)\big)\text{ rows}) \;=\; E_r(t),\qquad |t|\le1,
--   $$
--
--   and the conclusion is the paper's identity for all unit $u,v$.
--
--   Everything except that scalar integral is proved here: the pushforward of the Gaussian matrix law along $Z\mapsto(Zu,Zv)$, the fact that the expectation depends on $u,v$ only through $u\cdot v$, and the orthogonal reduction to the canonical pair. So this node isolates the entire remaining content of Lemma 2.1 in one displayed identity about $r$ independent bivariate Gaussians.
--
--   **Formalization Note** Stated in terms of `Grothendieck.reducedLaw` and `Grothendieck.reducedIntegrand` of the definition node `Grothendieck_Reduced`. A reduction, not a proof of the leaf: `Grothendieck.matrix_grothendieck_identity` follows from it once the bivariate integral is evaluated.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Lemma 2.1, p. 84, and Algorithm A, p. 82.

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian
import Definitions.Def_Grothendieck_Reduced

open MeasureTheory ProbabilityTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **Lemma 2.1, reduced to a single scalar identity.** If for every rank `r` and every
`t ∈ [-1,1]` the integral of `reducedIntegrand r` against `reducedLaw r t` equals `Er r t`,
then the matrix Grothendieck identity holds in full — including the case `|u·v| = 1`. -/
theorem matrix_grothendieck_identity_of_canonical
    (H : ∀ (r : ℕ) (t : ℝ), |t| ≤ 1 →
      ∫ W, reducedIntegrand r W ∂(reducedLaw r t) = Er r t)
    (r n : ℕ) (hr : 1 ≤ r) (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation r n u v = Er r (inner ℝ u v) := by sorry

end Grothendieck
