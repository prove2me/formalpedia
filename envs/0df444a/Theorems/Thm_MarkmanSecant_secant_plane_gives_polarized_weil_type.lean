-- Prove2me | Theorems.Thm_MarkmanSecant_secant_plane_gives_polarized_weil_type
-- name    : MarkmanSecant.secant_plane_gives_polarized_weil_type
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T15:28:00.970906+00:00
-- url     : https://prove2.me/theorems/b8042591-a888-44fd-98a5-ffb0a850ce21
-- title:
--   Proposition 2.4.4: the $K$-secant $P$ of (2.4.5) makes $X\times\hat X$ a polarized abelian variety of Weil type
-- statement:
--   **Proposition 2.4.4 of Markman, arXiv:2502.03415, together with (2.4.6) and Lemma 2.2.6.**
--
--   Let $X$ be a complex torus of dimension $n\ge2$ with complex structure $J$ ($J^2=-1$) and let $\Theta\in H^{1,1}(X,\mathbb{Z})$ be an ample class. Let $d$ be a positive integer, $\sqrt{-d}=i\sqrt d$, $K=\mathbb{Q}(\sqrt{-d})$, $u=\sqrt{-d}\,\Theta$ and $\bar u=-\sqrt{-d}\,\Theta$. Then:
--
--   1. $\exp(u)$ and $\exp(\bar u)$ are even pure spinors, and their maximal isotropic annihilators satisfy $W_1\cap W_2=0$;
--   2. there is a rational endomorphism $f$ of $V_{\mathbb{Q}}=H^1(X,\mathbb{Q})\oplus H^1(\hat X,\mathbb{Q})$ acting by $\sqrt{-d}$ on $W_1$ and by $-\sqrt{-d}$ on $W_2$, such that
--   $$f^2=-d,\qquad (f(x),f(y))_V=d\,(x,y)_V,\qquad f\circ I=I\circ f,$$
--   where $I$ is the complex structure of $X\times\hat X$;
--   3. $\dim_{\mathbb{C}}W_1\cap V^{1,0}=\dim_{\mathbb{C}}W_2\cap V^{1,0}=n$ (Weil's condition);
--   4. the symmetric form $g_P(x,y)=(f(I(x)),y)_V$ is negative definite on $V_{\mathbb{R}}$:
--   $$g_P(x,x)<0\quad\text{for all }0\neq x\in V_{\mathbb{R}}.$$
--
--   Together: $K$ acts on $X\times\hat X$ through $\eta(\sqrt{-d})=f$, Weil's condition holds, and the $(1,1)$-form $\Xi_P(x,y)=(f(x),y)_V$ is definite, so $(X\times\hat X,\eta,\Xi_P)$ is a polarized abelian variety of Weil type of dimension $2n$ attached to the rational $K$-secant $P=\operatorname{span}\{\operatorname{Re}\exp(u),\operatorname{Im}\exp(u)/\sqrt d\}$.
--
--   **Formalization Note.** Ampleness of $\Theta$ uses the sign convention of the proof of Proposition 2.4.4: $\Theta(a\wedge I(a))>0$ for nonzero $a\in H^1(\hat X,\mathbb{R})$, with $I=-J^{\mathsf T}$ on $H^1(\hat X,\mathbb{R})$. Negative definiteness is stated for the real part of $g_P(x,x)$, which is real for real $x$.
-- source:
--   E. Markman, Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds, arXiv:2502.03415v2 (8 Jun 2025), https://arxiv.org/abs/2502.03415

import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra

namespace MarkmanSecant

theorem secant_plane_gives_polarized_weil_type (n : ℕ) (hn : 2 ≤ n)
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1)
    (Θ : Spinor n) (hΘ : IsAmpleClass J Θ) (d : ℕ) (hd : 0 < d) :
    IsEvenPureSpinor (expS (sqrtNeg d • Θ)) ∧ IsEvenPureSpinor (expS ((-sqrtNeg d) • Θ)) ∧
      annih (expS (sqrtNeg d • Θ)) ⊓ annih (expS ((-sqrtNeg d) • Θ)) = ⊥ ∧
      ∃ F : Matrix (VIdx n) (VIdx n) ℚ,
        (∀ v ∈ annih (expS (sqrtNeg d • Θ)), (ratMatV F).mulVec v = sqrtNeg d • v) ∧
        (∀ v ∈ annih (expS ((-sqrtNeg d) • Θ)), (ratMatV F).mulVec v = (-sqrtNeg d) • v) ∧
        F * F = -((d : ℚ) • (1 : Matrix (VIdx n) (VIdx n) ℚ)) ∧
        (∀ x y : VIdx n → ℚ,
          pairV (ratV (F.mulVec x)) (ratV (F.mulVec y)) = (d : ℂ) * pairV (ratV x) (ratV y)) ∧
        ratMatV F * IV J = IV J * ratMatV F ∧
        Module.finrank ℂ ↥(annih (expS (sqrtNeg d • Θ)) ⊓ V10 J) = n ∧
        Module.finrank ℂ ↥(annih (expS ((-sqrtNeg d) • Θ)) ⊓ V10 J) = n ∧
        ∀ x : VIdx n → ℝ, x ≠ 0 →
          (pairV ((ratMatV F).mulVec ((IV J).mulVec (realV x))) (realV x)).re < 0 := by sorry

end MarkmanSecant
