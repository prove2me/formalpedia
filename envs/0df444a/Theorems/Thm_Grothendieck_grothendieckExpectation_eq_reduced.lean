-- Prove2me | Theorems.Thm_Grothendieck_grothendieckExpectation_eq_reduced
-- name    : Grothendieck.grothendieckExpectation_eq_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:18:12.686843+00:00
-- url     : https://prove2.me/theorems/987ff494-7901-459f-9d43-d61f9b35019b
-- title:
--   Lemma 2.1, two-column reduction: the rounding expectation depends only on $\langle u,v\rangle$
-- statement:
--   Let $Z$ be a random $r\times n$ matrix with independent standard Gaussian entries, and let $u,v\in\mathbb{R}^n$ be unit vectors. Write $Zu, Zv\in\mathbb{R}^r$ for the two Gaussian vectors and $\langle \cdot,\cdot\rangle$ for the Euclidean inner product. The rounding expectation
--   $$\mathbb{E}\Big[\Big\langle \frac{Zu}{\|Zu\|},\frac{Zv}{\|Zv\|}\Big\rangle\Big]$$
--   depends only on $t=\langle u,v\rangle$: it equals the integral of the cosine of the angle between the two columns of a random $r\times 2$ matrix $W$ whose $r$ rows are independent centred bivariate Gaussians with covariance matrix $\begin{pmatrix}1&t\\t&1\end{pmatrix}$.
--
--   This is the change of variables that turns the matrix Grothendieck identity (Lemma 2.1 of Briët–de Oliveira Filho–Vallentin) into a two-dimensional computation: it identifies every appearance of the ambient dimension $n$ and of the individual vectors $u$, $v$ with the one scalar $t=\langle u,v\rangle$.
--
--   **Formalization note.** The law of the pair is `reducedLaw r t` and the cosine is `reducedIntegrand r`; the statement is the bridge between the Gaussian model of the paper and the two-column model in which the series $E_r$ is computed.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - Lemma 2.1, p. 84; the change of variables to the two-column law used in the proof of equation (2.1).

import Mathlib
import Definitions.Def_Grothendieck_Gaussian
import Definitions.Def_Grothendieck_Reduced

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The two-column reduction.** The Gaussian-rounding expectation of `Zu/‖Zu‖` against
`Zv/‖Zv‖` is the integral of the cosine of the angle between the two columns against the law
of the pair `(Zu, Zv)`: `r` independent two-dimensional Gaussians of covariance
`!![1, t; t, 1]`, `t = ⟪u, v⟫`. In particular the expectation depends only on `⟪u, v⟫`. -/
theorem grothendieckExpectation_eq_reduced {r n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation r n u v
      = ∫ W, reducedIntegrand r W ∂(reducedLaw r (inner ℝ u v)) := by sorry

end Grothendieck
