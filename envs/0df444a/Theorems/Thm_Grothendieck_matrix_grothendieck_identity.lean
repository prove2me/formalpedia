-- Prove2me | Theorems.Thm_Grothendieck_matrix_grothendieck_identity
-- name    : Grothendieck.matrix_grothendieck_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T04:15:36.469344+00:00
-- url     : https://prove2.me/theorems/2b8a79cf-8343-4b1e-991c-3736cda7a067
-- title:
--   Lemma 2.1 — a matrix version of Grothendieck's identity
-- statement:
--   Let $u,v$ be unit vectors in $\mathbb R^n$ and let $Z\in\mathbb R^{r\times n}$ be a random matrix whose entries are independent standard normal random variables. Then
--
--   $$
--   \mathbb E\Big[\frac{Zu}{\lVert Zu\rVert}\cdot\frac{Zv}{\lVert Zv\rVert}\Big]
--   =\frac2r\Big(\frac{\Gamma((r+1)/2)}{\Gamma(r/2)}\Big)^2(u\cdot v)\;{}_2F_1\!\Big(\begin{smallmatrix}1/2,\,1/2\\ r/2+1\end{smallmatrix};(u\cdot v)^2\Big)
--   =\sum_{k\ge0}C_r\frac{(1/2)_k(1/2)_k}{(r/2+1)_k\,k!}(u\cdot v)^{2k+1},
--   $$
--
--   with $C_r=\frac2r(\Gamma((r+1)/2)/\Gamma(r/2))^2$ and $(a)_k$ the rising factorial; that is, the expected inner product of the two normalized Gaussian projections equals the hypergeometric series $E_r(u\cdot v)$.
--
--   This is the paper's matrix version of Grothendieck's identity, replacing the arcsine function of the classical identity by a hypergeometric function. At $r=1$ it reduces to $\mathbb E[\operatorname{sign}(Zu)\operatorname{sign}(Zv)]=\frac2\pi\arcsin(u\cdot v)$, the identity behind the Goemans-Williamson analysis of MAX CUT; at $r=2$ it reduces to Haagerup's elliptic-integral formula for the complex Grothendieck constant. The general case is the analytical core of the paper: combined with the vector construction of Lemma 4.1 it is what produces the factor $\beta(r,G)$ in $K(r,G)\le\beta(r,G)^{-1}$.
--
--   **Formalization Note** The left-hand side is `grothendieckExpectation r n u v`, an integral against the law of the Gaussian matrix (`Measure.pi` of `gaussianReal 0 1` over the entries); the right-hand side is `Er r (inner ℝ u v)`, the hypergeometric series of the definition layer.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, Lemma 2.1, p. 84, equation (2.1). https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian

namespace Grothendieck

theorem matrix_grothendieck_identity (r n : ℕ) (hr : 1 ≤ r) (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation r n u v = Er r (inner ℝ u v) := by sorry

end Grothendieck
