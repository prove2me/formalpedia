-- Prove2me | Theorems.Thm_Grothendieck_grothendieckExpectation_self
-- name    : Grothendieck.grothendieckExpectation_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:18:12.044442+00:00
-- url     : https://prove2.me/theorems/aa8a96f1-ab80-4be6-b765-6f431b3a1c62
-- title:
--   Lemma 2.1 at $|\tau|=1$: the Gaussian column does not vanish
-- statement:
--   Let $Z$ be a random $r\times n$ matrix with independent standard Gaussian entries, $r\ge 1$, and let $u\in\mathbb{R}^n$ be a unit vector. Then
--   $$\mathbb{E}\Big[\Big\langle \frac{Zu}{\|Zu\|},\frac{Zu}{\|Zu\|}\Big\rangle\Big] = 1 .$$
--   Indeed $Zu$ is a nondegenerate centred Gaussian vector in $\mathbb{R}^r$ (its covariance is the identity, because $\|u\|=1$), so $Zu\neq 0$ almost surely; on that event the cosine of the angle of $Zu$ with itself is exactly $1$, and off it the convention $\|0\|^{-1}=0$ makes the integrand $0$.
--
--   This is the case $|\tau|=1$ of the matrix Grothendieck identity of Briët–de Oliveira Filho–Vallentin (Lemma 2.1), the endpoint that no formula for $|\tau|<1$ reaches: there the limit $E_r(1)=1$ has to be matched by an almost-sure statement about a Gaussian column rather than by a computation with the density of `reducedLaw`, which is singular at $\tau=1$.
--
--   **Formalization note.** Together with the identity for $|\tau|<1$ in ranks $r\ge 2$ and $r=1$ this closes Lemma 2.1; the mathematical content is the almost-sure nonvanishing of a nondegenerate Gaussian vector, i.e. the statement that a proper subspace of $\mathbb{R}^r$ is null for a nondegenerate centred Gaussian.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - Lemma 2.1, p. 84, endpoint |tau| = 1 with E_r(1) = 1 (their equation (2.1) at t = 1).

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The endpoint `|τ| = 1` of the matrix Grothendieck identity.** For a unit vector `u` the
two Gaussian columns `Zu` and `Zu` coincide, so the cosine of the angle between them is `1`
whenever `Zu ≠ 0`; in rank `r ≥ 1` a Gaussian column vanishes only on a null set. -/
theorem grothendieckExpectation_self {r n : ℕ} (hr : 1 ≤ r) (u : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) : grothendieckExpectation r n u u = 1 := by sorry

end Grothendieck
