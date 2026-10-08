-- Prove2me | Theorems.Thm_LemkeLCP_Existence_only_ray_Zss
-- name    : LemkeLCP.Existence.only_ray_Zss
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:04:13.978669+00:00
-- url     : https://prove2.me/theorems/c5339462-59ab-4f80-8356-89b35b2608c0
-- title:
--   p. 6, before (15) — E₀* is a ray of Z** contained in Z₀**, and the only one
-- statement:
--   Let $M$ be a real square matrix of order $n$, $q\in\mathbb R^n$, and let $k\in\mathbb R$ be chosen as in (12): every extreme point $(z,z_0)$ of $Z^*=\{(z,z_0) : z\ge0,\ z_0\ge0,\ Mz+z_0e-q\ge0\}$ satisfies $e^{\mathsf T}z<k$. Consider the bordered system of (13),
--   $$M^{**}=\begin{pmatrix} M & e\\ -e^{\mathsf T} & 0\end{pmatrix},\qquad q^{**}=\begin{pmatrix} q\\ -k\end{pmatrix},$$
--   in the variables $z^*=(z,z_0)$, so that $Z^{**}=\{z^*\ge 0 : w=Mz+z_0e-q\ge0,\ w_0=k-e^{\mathsf T}z\ge 0\}$, and let $Z_0^{**}$ be its subset where $z^{*\mathsf T}w^*=z_0w_0$, i.e. $z^{\mathsf T}w=0$. Let $E_0^*$ be the ray of (11),
--   $$E_0^*=\{(z,z_0) : z=0,\ z_0>\max_i q_i,\ z_0>0\}\qquad(w=z_0e-q).$$
--   Then $E_0^*$ is a ray of $Z^{**}$ (an open edge of $Z^{**}$ with exactly one end-point) contained in $Z_0^{**}$, and every ray of $Z^{**}$ contained in $Z_0^{**}$ equals $E_0^*$.
--
--   The page's sentences are "Note that $E_0^*$ is still a ray of $Z^{**}$. The additional constraint (12) ensures that it is the only ray of $Z^{**}$ contained in $Z_0^{**}$." This is what makes Theorem 2 applicable to $Z^{**}$ with $s$ the index of $z_0$, giving Lemma 2 (p. 6).
--
--   **Formalization Note** (11) as printed omits $z_0\ge 0$, which $Z^*$ requires; the set $E_0^*$ here adds $z_0>0$ (strict, so that the end-point $z_0=\max(0,\max_i q_i)$ is not on the open edge). Non-degeneracy of $Z^{**}$ is not assumed: neither the existence of the ray nor the argument of (15)–(17) for its uniqueness uses it. The choice of $k$ is kept; it forces $k>0$, without which $E_0^*$ need not be a ray of $Z^{**}$ ($k<0$ makes $Z^{**}$ empty).
-- source:
--   Lemke, Bimatrix equilibrium points and mathematical programming, hal-01885823v1, p. 6, (12)–(17), sentence before (15)

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem only_ray_Zss {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (k : ℝ) (hk : ∀ p ∈ Set.extremePoints ℝ (Zstar M q), ∑ i, p.1 i < k) :
    IsRay (Mss M) (qss q k) (E0ss q) ∧ E0ss q ⊆ Zs (Mss M) (qss q k) (Sum.inr ()) ∧
      ∀ E : Set (ι ⊕ Unit → ℝ), IsRay (Mss M) (qss q k) E →
        E ⊆ Zs (Mss M) (qss q k) (Sum.inr ()) → E = E0ss q := by sorry

end LemkeLCP.Existence
