-- Prove2me | Theorems.Thm_MarkmanSecant_weil_condition_of_secant_in_hodge_ring
-- name    : MarkmanSecant.weil_condition_of_secant_in_hodge_ring
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T15:06:54.126503+00:00
-- url     : https://prove2.me/theorems/79e76233-0a4e-431b-9f17-f84e78407c1e
-- title:
--   Lemma 2.2.6: for a $K$-secant in the Hodge ring, $W_i\cap V^{1,0}$ and $W_i\cap V^{0,1}$ are $n$-dimensional
-- statement:
--   **Lemma 2.2.6 of Markman, arXiv:2502.03415.**
--
--   Let $X$ be a complex torus of dimension $n$ with complex structure $J$ ($J^2=-1$), let $d>0$ be rational and $\sqrt{-d}=i\sqrt d$. Let $a,b$ lie in the Hodge ring $\bigoplus_pH^{p,p}(X,\mathbb{Q})$ and suppose that
--   $$\lambda_1=a+\sqrt{-d}\,b,\qquad \lambda_2=a-\sqrt{-d}\,b$$
--   are even pure spinors, with maximal isotropic annihilators $W_1,W_2\subset V_{\mathbb{C}}$. Let $V_{\mathbb{C}}=V^{1,0}\oplus V^{0,1}$ be the eigenspace decomposition of the complex structure $I$ of $X\times\hat X$. Then
--   $$\dim W_1\cap V^{1,0}=\dim W_2\cap V^{1,0}=\dim W_1\cap V^{0,1}=\dim W_2\cap V^{0,1}=n.$$
--
--   In other words, if the plane $P=\operatorname{span}_{\mathbb{Q}}(a,b)$ is contained in the Hodge ring, the $K$-structure defined by $P$ satisfies Weil's condition on $X\times\hat X$.
-- source:
--   E. Markman, Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds, arXiv:2502.03415v2 (8 Jun 2025), https://arxiv.org/abs/2502.03415

import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra

namespace MarkmanSecant

theorem weil_condition_of_secant_in_hodge_ring (n : ℕ)
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1)
    (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsInHodgeRing J a) (hb : IsInHodgeRing J b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b)) (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b)) :
    Module.finrank ℂ ↥(annih (a + sqrtNeg d • b) ⊓ V10 J) = n ∧
      Module.finrank ℂ ↥(annih (a - sqrtNeg d • b) ⊓ V10 J) = n ∧
      Module.finrank ℂ ↥(annih (a + sqrtNeg d • b) ⊓ V01 J) = n ∧
      Module.finrank ℂ ↥(annih (a - sqrtNeg d • b) ⊓ V01 J) = n := by sorry

end MarkmanSecant
