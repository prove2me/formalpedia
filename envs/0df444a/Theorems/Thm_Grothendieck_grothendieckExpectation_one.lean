-- Prove2me | Theorems.Thm_Grothendieck_grothendieckExpectation_one
-- name    : Grothendieck.grothendieckExpectation_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:00:07.118137+00:00
-- url     : https://prove2.me/theorems/db8d30f8-245c-4594-a052-8b91c4729f80
-- title:
--   Lemma 2.1 at rank $1$: $\mathbb E[\mathrm{sign}\cdot\mathrm{sign}]=\frac2\pi\arcsin$
-- statement:
--   Let $Z$ be a $1\times n$ standard Gaussian matrix — a single Gaussian row — and let $u,v\in\mathbb R^n$ be unit vectors. Then
--
--   $$
--   \mathbb E\Big[\frac{Zu}{\lVert Zu\rVert}\cdot\frac{Zv}{\lVert Zv\rVert}\Big]=\frac2\pi\arcsin\,(u\cdot v).
--   $$
--
--   This is Lemma 2.1 of the paper at rank $1$. At rank $1$ the two Gaussian projections are scalars, the normalization is the sign, and the identity reduces to the classical statement $\mathbb E[\operatorname{sign}(Zu)\operatorname{sign}(Zv)]=\frac2\pi\arcsin(u\cdot v)$ — the Gaussian-hyperplane picture behind the Goemans–Williamson analysis of MAX CUT, and the base case that no $r\ge2$ argument reaches (the Laplace-transform route through $\int_0^\infty s^{-1/2}e^{-s\lVert X\rVert^2}ds$ diverges at $r=1$).
--
--   The proof computes the expectation directly instead of quoting it. After the pushforward, the integrand is $\operatorname{sign}x\cdot\operatorname{sign}(tx+sy)$ against two independent standard Gaussians, with $t=u\cdot v$ and $s=\sqrt{1-t^2}$. Integrating the second variable gives $\Psi(c)=2\Phi(c)-1$ for the Gaussian distribution function $\Phi$; Fubini and evenness reduce the expectation to $2\int_0^{t/s}\varphi$, and differentiating under the integral gives $\Psi'(c)=\frac1\pi(1+c^2)^{-1}$, hence $\Psi(c)=\frac2\pi\arctan c$. The last step is $\arctan\big(t/\sqrt{1-t^2}\big)=\arcsin t$ for $|t|<1$, with $t=\pm1$ handled separately.
--
--   **Formalization Note** Combined with the published reduction `Grothendieck.matrix_grothendieck_identity_of_canonical` and the published `Grothendieck.Er_one_eq_arcsin`, this node is the hypothesis of that reduction at $r=1$; the matrix identity then needs only the $r\ge2$ half.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Lemma 2.1, p. 84, and the rank-one case $\frac2\pi\arcsin(u\cdot v)$ noted there.

import Mathlib
import Definitions.Def_Grothendieck_Gaussian

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **Lemma 2.1 at rank `r = 1`.** For unit `u v` in `ℝ^n`, the expected correlation of the two
Gaussian sign projections is `(2/π)·arcsin(u·v)` — Grothendieck's classical identity, which is the
`r = 1` case of the matrix identity and the case no `r ≥ 2` argument reaches. -/
theorem grothendieckExpectation_one {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation 1 n u v = 2 / Real.pi * Real.arcsin (inner ℝ u v) := by sorry

end Grothendieck
