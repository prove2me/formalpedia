-- Prove2me | Theorems.Thm_MarkmanSecant_exists_rational_similarity_of_secant
-- name    : MarkmanSecant.exists_rational_similarity_of_secant
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T15:08:32.865987+00:00
-- url     : https://prove2.me/theorems/43c59111-62f0-4248-90ba-b11d1db95e41
-- title:
--   Equations (2.2.4), (2.4.1): the rational similarity $f=\eta_{\sqrt{-d}}$ of a $K$-secant
-- statement:
--   **The similarity $f=\eta_{\sqrt{-d}}$ of Markman, arXiv:2502.03415, (2.2.4) and (2.4.1).**
--
--   Let $X$ be a complex torus of dimension $n$, let $d>0$ be rational and $\sqrt{-d}=i\sqrt d$. Let $a,b\in H^{\mathrm{ev}}(X,\mathbb{Q})$ be rational classes such that $\lambda_1=a+\sqrt{-d}\,b$ and $\lambda_2=a-\sqrt{-d}\,b$ are even pure spinors whose annihilators satisfy $W_1\cap W_2=0$. Then there is a rational endomorphism $f$ of $V_{\mathbb{Q}}=H^1(X,\mathbb{Q})\oplus H^1(\hat X,\mathbb{Q})$ such that
--
--   1. $f$ acts on $W_1$ by $\sqrt{-d}$ and on $W_2$ by $-\sqrt{-d}$ (after extending scalars to $\mathbb{C}$);
--   2. $f^2=-d$;
--   3. $f$ is a similarity: $(f(x),f(y))_V=d\,(x,y)_V$ for all $x,y\in V_{\mathbb{Q}}$.
--
--   Such an $f$ defines the action $\eta:K\to\operatorname{End}_{\mathbb{Q}}(V_{\mathbb{Q}})$, $\eta(\sqrt{-d})=f$, of $K=\mathbb{Q}(\sqrt{-d})$ on $V_{\mathbb{Q}}$.
--
--   **Formalization Note.** The source assumes $P$ non-isotropic and derives $W_1\cap W_2=0$ from Lemma 2.2.1; here $W_1\cap W_2=0$ is the hypothesis. Endomorphisms of $V_{\mathbb{Q}}$ are rational $4n\times4n$ matrices.
-- source:
--   E. Markman, Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds, arXiv:2502.03415v2 (8 Jun 2025), https://arxiv.org/abs/2502.03415

import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra

namespace MarkmanSecant

theorem exists_rational_similarity_of_secant (n : ℕ) (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsRationalClass a) (hb : IsRationalClass b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b)) (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥) :
    ∃ F : Matrix (VIdx n) (VIdx n) ℚ,
      (∀ v ∈ annih (a + sqrtNeg d • b), (ratMatV F).mulVec v = sqrtNeg d • v) ∧
      (∀ v ∈ annih (a - sqrtNeg d • b), (ratMatV F).mulVec v = (-sqrtNeg d) • v) ∧
      F * F = -(d • (1 : Matrix (VIdx n) (VIdx n) ℚ)) ∧
      ∀ x y : VIdx n → ℚ,
        pairV (ratV (F.mulVec x)) (ratV (F.mulVec y)) = (d : ℂ) * pairV (ratV x) (ratV y) := by sorry

end MarkmanSecant
