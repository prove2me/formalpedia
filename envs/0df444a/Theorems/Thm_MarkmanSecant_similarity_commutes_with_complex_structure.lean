-- Prove2me | Theorems.Thm_MarkmanSecant_similarity_commutes_with_complex_structure
-- name    : MarkmanSecant.similarity_commutes_with_complex_structure
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T15:25:00.783879+00:00
-- url     : https://prove2.me/theorems/93cddb0a-09ff-4c80-a84b-6aedca40b4be
-- title:
--   §2.4, p. 20: $f=\eta_{\sqrt{-d}}$ commutes with the complex structure $I$ of $X\times\hat X$
-- statement:
--   **$f$ commutes with $I$ (Markman, arXiv:2502.03415, §2.4, p. 20; a consequence of Lemma 2.2.6).**
--
--   Let $X$ be a complex torus of dimension $n$ with complex structure $J$ ($J^2=-1$), let $d>0$ be rational and $\sqrt{-d}=i\sqrt d$. Let $a,b$ lie in the Hodge ring $\bigoplus_pH^{p,p}(X,\mathbb{Q})$, suppose that $\lambda_{1,2}=a\pm\sqrt{-d}\,b$ are even pure spinors with $W_1\cap W_2=0$, and let $f$ be a rational endomorphism of $V_{\mathbb{Q}}$ acting by $\sqrt{-d}$ on $W_1$ and by $-\sqrt{-d}$ on $W_2$. Then
--   $$f\circ I=I\circ f,$$
--   where $I=J\oplus(-J^{\mathsf T})$ is the complex structure of $V_{\mathbb{R}}=H^1(X\times\hat X,\mathbb{R})$.
--
--   Consequently $f$ respects the complex structure of the torus $X\times\hat X$, so $\eta(\sqrt{-d})=f$ embeds $K$ into $\operatorname{End}_{\mathbb{Q}}(X\times\hat X)$.
-- source:
--   E. Markman, Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds, arXiv:2502.03415v2 (8 Jun 2025), https://arxiv.org/abs/2502.03415

import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra

namespace MarkmanSecant

theorem similarity_commutes_with_complex_structure (n : ℕ)
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1)
    (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsInHodgeRing J a) (hb : IsInHodgeRing J b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b)) (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥)
    (F : Matrix (VIdx n) (VIdx n) ℚ)
    (hF₁ : ∀ v ∈ annih (a + sqrtNeg d • b), (ratMatV F).mulVec v = sqrtNeg d • v)
    (hF₂ : ∀ v ∈ annih (a - sqrtNeg d • b), (ratMatV F).mulVec v = (-sqrtNeg d) • v) :
    ratMatV F * IV J = IV J * ratMatV F := by sorry

end MarkmanSecant
