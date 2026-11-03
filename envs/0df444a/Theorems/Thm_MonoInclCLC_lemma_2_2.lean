-- Prove2me | Theorems.Thm_MonoInclCLC_lemma_2_2
-- name    : MonoInclCLC.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:07.960014+00:00
-- url     : https://prove2.me/theorems/b28f2376-b7ce-4f03-b6e6-cc2c071b5cc3
-- title:
--   Lemma 2.2, p.5 — two-sided growth of $\varphi$ in $\lambda$, and its zeros
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $A:\mathcal H\rightrightarrows\mathcal H$ a maximal monotone operator with $A^{-1}(0)=\{x:0\in Ax\}\neq\emptyset$. For an integer $p\ge 2$ let $\varphi(\lambda,x)=\lambda^{1/(p-1)}\|x-(I+\lambda A)^{-1}x\|$ for $\lambda>0$, and $\varphi(0,x)=0$. Then, for all $x\in\mathcal H$ and $0<\lambda_1\le\lambda_2$,
--   $$
--   \Big(\frac{\lambda_2}{\lambda_1}\Big)^{\frac{1}{p-1}}\varphi(\lambda_1,x)\le\varphi(\lambda_2,x)\le\Big(\frac{\lambda_2}{\lambda_1}\Big)^{\frac{p}{p-1}}\varphi(\lambda_1,x).
--   $$
--   Moreover, for any fixed $\lambda>0$, $\varphi(\lambda,x)=0$ if and only if $0\in Ax$.
--
--   This extends the classical estimates for $p=2$ to all $p\ge 2$, and it is the source of the monotonicity of $\varphi$ in $\lambda$.
--
--   Differences from the source:
--   - encoding: the resolvent (I + λA)⁻¹ as an operator determined by A → a family J with IsResolvent l A (J l) for every l > 0; reason: for maximal monotone A such a map exists (Minty) and is unique (monotonicity), so no instance changes
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Lemma 2.2, p.5

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_phi

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoInclCLC

/-- **Lemma 2.2** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Lemma 2.2, p.5): for `p ≥ 2`, all `x` and `0 < λ₁ ≤ λ₂`,
`(λ₂/λ₁)^(1/(p-1)) ϕ(λ₁, x) ≤ ϕ(λ₂, x) ≤ (λ₂/λ₁)^(p/(p-1)) ϕ(λ₁, x)`; and `ϕ(λ, x) = 0` if and only
if `0 ∈ Ax`, for any fixed `λ > 0`.

**Formalization Note.** `J l` is the resolvent `(I + l A)⁻¹` for `l > 0`. The standing assumptions of p.3 are hypotheses. -/
theorem lemma_2_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 2 ≤ p) :
    (∀ (x : H) (l₁ l₂ : ℝ), 0 < l₁ → l₁ ≤ l₂ →
      (l₂ / l₁) ^ (1 / ((p : ℝ) - 1)) * phi J p l₁ x ≤ phi J p l₂ x ∧
        phi J p l₂ x ≤ (l₂ / l₁) ^ ((p : ℝ) / ((p : ℝ) - 1)) * phi J p l₁ x) ∧
    (∀ (x : H) (l : ℝ), 0 < l → (phi J p l x = 0 ↔ (0 : H) ∈ A x)) := by sorry

end MonoInclCLC
