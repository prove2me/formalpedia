-- Prove2me | Theorems.Thm_MTT_Cohomology_reflection_class
-- name    : MTT.Cohomology.reflection_class
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-06T15:49:28.287725+00:00
-- url     : https://prove2.me/theorems/c85142f2-67d2-4548-b57b-a469f28c8e7b
-- title:
--   The reflection is a Hecke-equivariant involution on modular symbols
-- statement:
--   Write $J=\begin{pmatrix}-1&0\\0&1\end{pmatrix}$ and let
--   $$(\mathcal R\varphi)(x,y) = J\cdot\varphi(Jx,\,Jy)$$
--   be the reflection operator on cocycles of weight $n$ with coefficients in a commutative ring $R$; on
--   cusps $J$ acts by $r\mapsto -r$ and fixes $\infty$, and on binary forms by $X\mapsto -X$, $Y\mapsto Y$.
--   This is the involution whose $\pm 1$-eigenspaces cut out the signed modular symbols. The theorem
--   asserts three things about $\mathcal R$ on
--   $H^1_c(\Gamma_1(N),\operatorname{Sym}^n R^2)$.
--
--   **(i) $\mathcal R$ preserves the space.** If $\varphi$ is a $\Gamma_1(N)$-equivariant cocycle with
--   values in $\operatorname{Sym}^n$, so is $\mathcal R\varphi$. Equivariance uses that
--   $J\Gamma_1(N)J^{-1}=\Gamma_1(N)$, since conjugation by $J$ sends
--   $\begin{pmatrix}a&b\\c&d\end{pmatrix}$ to $\begin{pmatrix}a&-b\\-c&d\end{pmatrix}$.
--
--   **(ii) $\mathcal R$ commutes with the prime Hecke operators.** For every $\ell$ and every scalar
--   $e\in R$,
--   $$\mathcal R\bigl(T_\ell^{(e)}\varphi\bigr)=T_\ell^{(e)}\bigl(\mathcal R\varphi\bigr),
--   \qquad T_\ell^{(e)}=\sum_{b=0}^{\ell-1}\Bigl|\begin{pmatrix}1&b\\0&\ell\end{pmatrix}
--   + e\Bigl|\begin{pmatrix}\ell&0\\0&1\end{pmatrix}.$$
--   The identity comes from $J\begin{pmatrix}1&b\\0&\ell\end{pmatrix}J=\begin{pmatrix}1&-b\\0&\ell\end{pmatrix}$
--   together with $\begin{pmatrix}1&-b\\0&\ell\end{pmatrix}=\begin{pmatrix}1&-1\\0&1\end{pmatrix}\begin{pmatrix}1&\ell-b\\0&\ell\end{pmatrix}$:
--   the coset representatives are permuted by $b\mapsto \ell-b \pmod \ell$, and the leftover unipotent
--   matrix lies in $\Gamma_1(N)$, so it acts trivially on $\varphi$. The second term is fixed because
--   $J$ commutes with $\operatorname{diag}(\ell,1)$.
--
--   **(iii) $\mathcal R$ preserves the nebentype law.** If $\varphi$ satisfies
--   $\varphi(\gamma x,\gamma y)=e(d)\,\gamma\cdot\varphi(x,y)$ for all $\gamma\in\Gamma_0(N)$, then so
--   does $\mathcal R\varphi$, with the same character $e$; conjugation by $J$ preserves $\Gamma_0(N)$ and
--   leaves the lower-right entry $d$ unchanged.
--
--   Together these say that $\mathcal R$ is an involution of the Hecke module of modular symbols, so the
--   signed projections $\tfrac12(1\pm\mathcal R)$ are Hecke-equivariant idempotents. This is the algebraic
--   input behind every "plus/minus modular symbol" construction.
-- source:
--   Mazur-Tate-Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), 1-48, I.§1-§4 (signed modular symbols); Ash-Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §4, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf; J. E. Cremona, Algorithms for Modular Elliptic Curves, 2nd ed., CUP 1997, §2.1-2.4.

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.reflection_class {N n : ℕ} {R : Type*} [CommRing R] (φ : Hc N n R) :
    (∃ ψ : Hc N n R, ψ.val = reflection φ.val) ∧
    (∀ (e : R) (l : ℕ), reflection (primeHecke e l φ.val)
        = primeHecke e l (reflection φ.val)) ∧
    (∀ (e : ZMod N → R),
      (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
        φ.val (cuspAct γ.val x, cuspAct γ.val y)
          = e (γ.val 1 1 : ZMod N) • act γ.val.val (φ.val (x, y))) →
      ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
        reflection φ.val (cuspAct γ.val x, cuspAct γ.val y)
          = e (γ.val 1 1 : ZMod N) • act γ.val.val (reflection φ.val (x, y))) := by sorry
