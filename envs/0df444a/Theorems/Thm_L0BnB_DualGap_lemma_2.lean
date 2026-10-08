-- Prove2me | Theorems.Thm_L0BnB_DualGap_lemma_2
-- name    : L0BnB.DualGap.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:29:19.297951+00:00
-- url     : https://prove2.me/theorems/23a963d7-078c-4f96-8e96-431b62c65595
-- title:
--   Lemma 2 — per-coordinate perturbation bound for the dual term v
-- statement:
--   Assume $\sqrt{\lambda_0/\lambda_2}\le M$ (with $\lambda_0,\lambda_2,M>0$), that every column of $X\in\mathbb R^{n\times p}$ has unit $\ell_2$ norm and that $\|y\|_2=1$. Let $\beta^*$ be an optimal solution of (5), with $r^*=y-X\beta^*$, and $\alpha^*,\gamma^*$ the dual variables (23). Let $\hat\beta$ be a solution from Algorithm 2: $\|\hat\beta\|_\infty\le M$ and the set $V$ of Step 2 is empty. Let $(\hat\alpha,\hat\gamma)$ be the dual solution (25): $\hat\alpha=-(y-X\hat\beta)$ and $\hat\gamma$ maximizes $h_1(\hat\alpha,\cdot)$. Put $\epsilon=\|X(\beta^*-\hat\beta)\|_2$. Then
--
--   1. for every $i\in\operatorname{Supp}(\hat\beta)^c$, $v(\hat\alpha,\hat\gamma_i)=0$;
--   2. for every $i\in\operatorname{Supp}(\hat\beta)$,
--   $$
--   v(\hat\alpha,\hat\gamma_i)\le c_i\epsilon+(4\lambda_2)^{-1}\epsilon^2+v(\alpha^*,\gamma^*_i),\qquad(50)
--   $$
--   where $c_i=(2\lambda_2)^{-1}$ if $|\beta^*_i|<M$ and $c_i=M$ if $|\beta^*_i|=M$.
--
--   The lemma localizes the loss of the dual bound to the support of $\hat\beta$: outside it, the emptiness of $V$ makes the dual term vanish.
--
--   **Formalization Note** "A solution from Algorithm 2" is modelled by the two properties the paper uses: box feasibility and $V=\emptyset$ (Remark 1). $\gamma^*$ is the formula (23); its optimality (Theorem 2) is not assumed.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 31, Lemma 2, (50); proof p. 32

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals

namespace L0BnB.DualGap

/-- Lemma 2, p. 31: for `√(λ₀/λ₂) ≤ M`, unit-norm columns of `X` and `‖y‖₂ = 1`, `β*` optimal for (5),
`β̂` an output of Algorithm 2 (box-feasible with `V = ∅`), `α̂ = −r̂` and `γ̂ ∈ argmax h₁(α̂, ·)` (25),
and `ϵ = ‖X(β* − β̂)‖₂`: `v(α̂, γ̂ᵢ) = 0` for `i ∉ Supp(β̂)`, and
`v(α̂, γ̂ᵢ) ≤ cᵢϵ + (4λ₂)⁻¹ϵ² + v(α*, γ*ᵢ)` (50) for `i ∈ Supp(β̂)`. -/
theorem lemma_2 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : Real.sqrt (lam0 / lam2) ≤ M)
    (hX : ∀ i, ∑ r, X r i ^ 2 = 1) (hy : ∑ r, y r ^ 2 = 1)
    (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat : Fin p → ℝ) (hbox : βhat ∈ L0BnB.Reduced.box p M) (hV : Vset X y lam0 lam2 M βhat = ∅)
    (γhat : Fin p → ℝ) (hγ : IsGammaHat X y lam0 lam2 M βhat γhat) :
    (∀ i, βhat i = 0 → v X lam0 lam2 M (alphaHat X y βhat) (γhat i) i = 0) ∧
    (∀ i, βhat i ≠ 0 →
      v X lam0 lam2 M (alphaHat X y βhat) (γhat i) i ≤
        cLemma2 lam2 M βs i * primalGap X βs βhat + (4 * lam2)⁻¹ * primalGap X βs βhat ^ 2
          + v X lam0 lam2 M (L0BnB.Duality.alphaStar X y βs) (L0BnB.Duality.gammaStar X y lam2 M βs i) i) := by sorry

end L0BnB.DualGap
