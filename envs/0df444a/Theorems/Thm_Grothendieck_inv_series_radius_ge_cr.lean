-- Prove2me | Theorems.Thm_Grothendieck_inv_series_radius_ge_cr
-- name    : Grothendieck.inv_series_radius_ge_cr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-02T04:16:41.047514+00:00
-- url     : https://prove2.me/theorems/25cc2bb6-bb87-4e38-8df9-525fa90fe9f5
-- title:
--   Lemma 3.2 — the series of $E_r^{-1}$ converges in the disc of radius $c_r$
-- statement:
--   Let $r\ge1$ and let
--
--   $$
--   c_r=\min\{|E_r(e^{it})|:t\in[0,2\pi]\}
--   $$
--
--   be the minimum modulus of $E_r$ on the unit circle. Then the Taylor series at the origin of the inverse function,
--
--   $$
--   E_r^{-1}(t)=\sum_{k\ge0}b_{2k+1}t^{2k+1},
--   $$
--
--   has radius of convergence at least $c_r$: for every complex $z$ with $|z|<c_r$ the series $\sum_k b_{2k+1}z^{2k+1}$ converges.
--
--   The proof expresses $E_r^{-1}$ as the contour integral
--
--   $$
--   E_r^{-1}(z)=\frac{1}{2\pi i}\int_{\partial D}w\,\frac{E_r'(w)}{E_r(w)-z}\,dw
--   $$
--
--   around the unit circle and expands the integrand in a geometric series in $z/E_r(w)$, which converges uniformly on $\partial D$ as soon as $|z|<c_r$; Proposition 3.3 (a unique simple zero of $E_r$ in the disc) is what makes the residue theorem applicable. This is the quantitative control the rounding argument needs: it says the expansion of $E_r^{-1}$ may be used on a disc around the origin, not merely in a neighbourhood of it.
--
--   **Formalization Note** Convergence of $\sum_k b_{2k+1}z^{2k+1}$ at every $\lVert z\rVert<c_r$ is stated as summability of the family $(b_{2k+1}z^{2k+1})_{k\ge0}$ in $\mathbb C$; $b_j=(E_r^{-1})^{(j)}(0)/j!$ and $c_r$ is the `sInf` of the modulus of $E_r$ over the unit circle, restricted to $t\in[0,2\pi]$.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, Lemma 3.2, p. 88, with $c_r$ as in equation (3.3), p. 88. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Series

namespace Grothendieck

theorem inv_series_radius_ge_cr (r : ℕ) (hr : 1 ≤ r) (z : ℂ) (hz : ‖z‖ < cr r) :
    Summable fun k : ℕ => (invCoeff r (2 * k + 1) : ℂ) * z ^ (2 * k + 1) := by sorry

end Grothendieck
