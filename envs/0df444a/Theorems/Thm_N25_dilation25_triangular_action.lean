-- Prove2me | Theorems.Thm_N25_dilation25_triangular_action
-- name    : N25.dilation25_triangular_action
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:11.05449+00:00
-- url     : https://prove2.me/theorems/9bdcb800-d044-49cc-9592-8b99126c3f5a
-- title:
--   A triangular factorization gives the corresponding upper-half-plane change of variables
-- statement:
--   Let $A,B\in\mathrm{SL}_2(\mathbb Z)$ and let $d,e,v\in\mathbb Z$ with $d>0$ and $e>0$. Assume
--
--   $$\begin{pmatrix}25&0\0&1\end{pmatrix}A=B\begin{pmatrix}d&v\0&e\end{pmatrix}.$$
--
--   For every $\tau$ in the upper half-plane there exists $z$ in the upper half-plane with $z=(d\tau+v)/e$ and $Bz=25(A\tau)$. This supplies the analytic variable change associated with the cusp factorization.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open Filter Topology

theorem N25.dilation25_triangular_action
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d e v : ℤ)
    (hd : 0 < d) (he : 0 < e)
    (h : !![(25 : ℤ), 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) ℤ) =
      (B : Matrix (Fin 2) (Fin 2) ℤ) * !![d, v; 0, e]) (τ : UpperHalfPlane) :
    ∃ z : UpperHalfPlane, (z : ℂ) = ((d : ℂ) * (τ : ℂ) + (v : ℂ)) / (e : ℂ) ∧
      ((B • z : UpperHalfPlane) : ℂ) = 25 * ((A • τ : UpperHalfPlane) : ℂ) := by sorry
