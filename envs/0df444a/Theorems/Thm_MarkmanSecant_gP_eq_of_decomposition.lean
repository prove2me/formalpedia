-- Prove2me | Theorems.Thm_MarkmanSecant_gP_eq_of_decomposition
-- name    : MarkmanSecant.gP_eq_of_decomposition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T15:26:02.80546+00:00
-- url     : https://prove2.me/theorems/5862075c-5c6e-4ba9-8ed3-2e91191fe94b
-- title:
--   Lemma 2.4.2: $g_P(v,v)=2\sqrt d\,\big(-(v_1^{1,0},v_2^{0,1})_V+(v_1^{0,1},v_2^{1,0})_V\big)$
-- statement:
--   **Lemma 2.4.2 of Markman, arXiv:2502.03415.**
--
--   Keep the setting of Assumption 2.4.1: $X$ a complex torus of dimension $n$ with complex structure $J$ ($J^2=-1$), $d>0$ rational, $a,b$ in the Hodge ring with $\lambda_{1,2}=a\pm\sqrt{-d}\,b$ even pure spinors and $W_1\cap W_2=0$, and $f$ a rational endomorphism of $V_{\mathbb{Q}}$ acting by $\pm\sqrt{-d}$ on $W_{1,2}$. Let $I$ be the complex structure of $X\times\hat X$ and $g_P(x,y)=(f(I(x)),y)_V$.
--
--   Let $v\in V_{\mathbb{Q}}$ and let
--   $$v=v_1^{1,0}+v_2^{1,0}+v_1^{0,1}+v_2^{0,1},\qquad v_i^{1,0}\in W_i\cap V^{1,0},\ v_i^{0,1}\in W_i\cap V^{0,1}.$$
--   Then
--   $$g_P(v,v)=2\sqrt d\,\Big(-\big(v_1^{1,0},v_2^{0,1}\big)_V+\big(v_1^{0,1},v_2^{1,0}\big)_V\Big).$$
--
--   This computation reduces the definiteness of $g_P$ (Proposition 2.4.4) to the pairing between the pieces of $W_1$ and $W_2$.
-- source:
--   E. Markman, Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds, arXiv:2502.03415v2 (8 Jun 2025), https://arxiv.org/abs/2502.03415

import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra

namespace MarkmanSecant

theorem gP_eq_of_decomposition (n : ℕ)
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1)
    (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsInHodgeRing J a) (hb : IsInHodgeRing J b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b)) (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥)
    (F : Matrix (VIdx n) (VIdx n) ℚ)
    (hF₁ : ∀ v ∈ annih (a + sqrtNeg d • b), (ratMatV F).mulVec v = sqrtNeg d • v)
    (hF₂ : ∀ v ∈ annih (a - sqrtNeg d • b), (ratMatV F).mulVec v = (-sqrtNeg d) • v)
    (v : VIdx n → ℚ) (v₁₁₀ v₂₁₀ v₁₀₁ v₂₀₁ : VC n)
    (h₁₁₀ : v₁₁₀ ∈ annih (a + sqrtNeg d • b) ⊓ V10 J)
    (h₂₁₀ : v₂₁₀ ∈ annih (a - sqrtNeg d • b) ⊓ V10 J)
    (h₁₀₁ : v₁₀₁ ∈ annih (a + sqrtNeg d • b) ⊓ V01 J)
    (h₂₀₁ : v₂₀₁ ∈ annih (a - sqrtNeg d • b) ⊓ V01 J)
    (hv : ratV v = v₁₁₀ + v₂₁₀ + v₁₀₁ + v₂₀₁) :
    pairV ((ratMatV F).mulVec ((IV J).mulVec (ratV v))) (ratV v) =
      2 * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) * (-pairV v₁₁₀ v₂₀₁ + pairV v₁₀₁ v₂₁₀) := by sorry

end MarkmanSecant
