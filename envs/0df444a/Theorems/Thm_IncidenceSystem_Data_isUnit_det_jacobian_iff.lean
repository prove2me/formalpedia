-- Prove2me | Theorems.Thm_IncidenceSystem_Data_isUnit_det_jacobian_iff
-- name    : IncidenceSystem.Data.isUnit_det_jacobian_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/6cfe626d-6385-541f-a8b2-eeadf893701f
-- title:
--   Unit Jacobian criterion for the incidence system
-- statement:
--   Let $g,e,m'$ be natural numbers, $A$ a commutative ring, and $D$ an [`IncidenceSystem.Data g e m' A`](def/IncidenceSystem.html#L18), i.e. families of polynomials $G_{i,j}$, $p_{k,i}$, $s_{k,i}$ in $A[Y_o]$ with $o$ ranging over `Option (Fin e)` (here $i\in\mathrm{Fin}\,g$, $j\in\mathrm{Fin}\,e$, $k\in$ `Option (Fin (g*m'))`), together with constants $u_0,w_0,\sigma_0$. Let $pt$ assign an element of $A$ to each variable of `Var g e m'`, that is to each $u_i$, $w_{i,j,r}$, $\sigma_{k,i,r}$ ($r\in\mathrm{Fin}(m'+1)$) and $c_k$. Assume: $\partial G_{i,j}/\partial Y_{j'}=0$ as a polynomial whenever $j<j'$; $pt(c_k)=0$ for all $k$; $pt(\sigma_{\mathrm{none},i,r})$ equals $1$ for $r=0$ and $0$ otherwise; $p_{\mathrm{none},i}=(Y_{\mathrm{none}}-pt(u_i))^{m'+1}$ and $s_{\mathrm{none},i}=1$ for all $i$; every element `D.dG pt i j` of $A$ is a unit; and every `D.sVal pt k i`, the value of $s_{k,i}$ at the point sending $Y_{\mathrm{none}}\mapsto pt(u_i)$ and $Y_j\mapsto pt(w_{i,j,0})$, is a unit. Then the determinant of the square matrix `D.jacobian pt` indexed by `Var g e m'`, with $(v,v')$ entry the evaluation at $pt$ of $\partial/\partial v'$ of the $v$-th member of the system (`D.branch i j r` for $v=w_{i,j,r}$, `D.inv k i r` for $v=\sigma_{k,i,r}$, `D.inc i (Fin.last m')` for $v=u_i$, and `D.inc` at the index pair attached to $k$ for $v=c_k$), is a unit in $A$ if and only if both $((m'+1)\cdot 1_A)^g$ is a unit and the determinant of the $gm'\times gm'$ matrix `D.tcMatrix pt`, with entries the evaluations at $pt$ of `D.tc (some k')` at the index pair attached to $k$, is a unit.
--
--   This is the invertibility criterion for the Jacobian of the incidence system at a normalised point: an elementary consequence of the block-triangular shape of the Jacobian, which isolates the factor $(m'+1)^g$ and the determinant of the Taylor-coefficient matrix from the unit factors coming from the $G_{i,j}$ and the $s_{k,i}$. It is used to verify that the Jacobian at the centre of a prolongation tuple modelling $m$-division has unit determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IncidenceSystem_Data_isUnit_det_jacobian_iff.lean

import Mathlib
import Definitions.Def_IncidenceSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial IncidenceSystem

theorem IncidenceSystem.Data.isUnit_det_jacobian_iff
    {g e m' : ℕ} {A : Type*} [CommRing A] (D : IncidenceSystem.Data g e m' A) (pt : Var g e m' → A)
    (htri : ∀ i (j j' : Fin e), j < j' → MvPolynomial.pderiv (some j') (D.G i j) = 0)
    (hc : ∀ k, pt (Var.c k) = 0)
    (hσ : ∀ i r, pt (Var.σ none i r) = if (r : ℕ) = 0 then 1 else 0)
    (hp : ∀ i, D.p none i = (MvPolynomial.X none - MvPolynomial.C (pt (Var.u i))) ^ (m' + 1))
    (hs : ∀ i, D.s none i = 1)
    (hG : ∀ i j, IsUnit (D.dG pt i j)) (hsv : ∀ k i, IsUnit (D.sVal pt k i)) :
    IsUnit (D.jacobian pt).det ↔ IsUnit (((m' + 1 : ℕ) : A) ^ g) ∧ IsUnit (D.tcMatrix pt).det := by sorry
