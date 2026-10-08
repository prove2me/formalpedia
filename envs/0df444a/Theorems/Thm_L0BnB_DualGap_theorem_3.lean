-- Prove2me | Theorems.Thm_L0BnB_DualGap_theorem_3
-- name    : L0BnB.DualGap.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:29:46.086463+00:00
-- url     : https://prove2.me/theorems/a5aec423-d56a-45e4-8ea1-a8111548eef6
-- title:
--   Theorem 3 — dual bounds from the active-set primal solution lose only O(kϵ), independent of p
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ and $y\in\mathbb R^n$, where the columns of $X$ and $y$ have unit $\ell_2$ norm, and $\lambda_0,\lambda_2,M>0$. Let $\beta^*$ be an optimal solution of the reduced relaxation (5), with $(\alpha^*,\gamma^*)$ and $(\rho^*,\mu^*)$ the dual variables (23)–(24) of Theorem 2. Let $\hat\beta$ be an inexact solution obtained by Algorithm 2, i.e. $\|\hat\beta\|_\infty\le M$ and the violation set $V$ of Step 2 is empty. Define the primal gap $\epsilon=\|X(\beta^*-\hat\beta)\|_2$ and $k=\|\hat\beta\|_0$. Let $(\hat\alpha,\hat\gamma)$ be the dual solution (25) and $(\hat\rho,\hat\mu)$ the dual solution (27).
--
--   1. If $\sqrt{\lambda_0/\lambda_2}\le M$, then
--   $$
--   h_1(\hat\alpha,\hat\gamma)\ge h_1(\alpha^*,\gamma^*)-2\epsilon-\tfrac12\epsilon^2-\sum_{i\in\operatorname{Supp}(\hat\beta)}\big(c_i\epsilon+(4\lambda_2)^{-1}\epsilon^2\big),\qquad(55)
--   $$
--   with $c_i=(2\lambda_2)^{-1}$ if $|\beta^*_i|<M$ and $c_i=M$ if $|\beta^*_i|=M$. The sum has $k$ terms, so this is the paper's $h_1(\hat\alpha,\hat\gamma)\ge h_1(\alpha^*,\gamma^*)-kO(\epsilon)-kO(\epsilon^2)$ (29).
--   2. If $\sqrt{\lambda_0/\lambda_2}>M$, then
--   $$
--   h_2(\hat\rho,\hat\mu)\ge h_2(\rho^*,\mu^*)-\epsilon(2+Mk)-\epsilon^2/2,\qquad(59)
--   $$
--   which is the paper's $h_2(\hat\rho,\hat\mu)\ge h_2(\rho^*,\mu^*)-kO(\epsilon)-O(\epsilon^2)$ (30).
--
--   The constants depend only on $M$ and $\lambda_2$, and the number of features $p$ does not appear: the dual bounds computed from the cheap primal iterate lose an amount governed by the sparsity $k$ of the iterate.
--
--   **Formalization Note** The paper writes $O(\cdot)$; the proof yields (55) for (29) and (59) for (30), and these explicit forms are stated. "An inexact solution obtained using Algorithm 2" is modelled by box feasibility and $V=\emptyset$ (Remark 1), not by the iterations. $(\alpha^*,\gamma^*)$, $(\rho^*,\mu^*)$ are the formulas (23)–(24); their optimality for the duals is not assumed. $\hat\gamma$, $\hat\mu$ are arbitrary maximizers as in (25), (27). `sign` is `Real.sign` with $\operatorname{sign}(0)=0$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 15, Theorem 3, (29), (30); explicit constants from the proof, pp. 32–34, (55), (59)

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals

namespace L0BnB.DualGap

/-- Theorem 3, p. 15, with the constants of its proof (pp. 32–34). Assume the columns of `X` and `y`
have unit ℓ₂ norm (standing assumption of Section 3, p. 9). Let `β*` be optimal for (5), `β̂` an output of
Algorithm 2 (box-feasible with `V = ∅`), `ϵ = ‖X(β* − β̂)‖₂`, `k = ‖β̂‖₀`, `γ̂` as in (25) and `µ̂` as in (27).
If `√(λ₀/λ₂) ≤ M`, (55):
`h₁(α̂, γ̂) ≥ h₁(α*, γ*) − 2ϵ − ½ϵ² − ∑_{i ∈ Supp(β̂)} (cᵢϵ + (4λ₂)⁻¹ϵ²)`, the explicit form of (29).
If `√(λ₀/λ₂) > M`, (59): `h₂(ρ̂, µ̂) ≥ h₂(ρ*, µ*) − ϵ(2 + Mk) − ϵ²/2`, the explicit form of (30). -/
theorem theorem_3 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hX : ∀ i, ∑ r, X r i ^ 2 = 1) (hy : ∑ r, y r ^ 2 = 1)
    (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat : Fin p → ℝ) (hbox : βhat ∈ L0BnB.Reduced.box p M) (hV : Vset X y lam0 lam2 M βhat = ∅)
    (γhat : Fin p → ℝ) (hγ : IsGammaHat X y lam0 lam2 M βhat γhat)
    (μhat : Fin p → ℝ) (hμ : IsMuHat X y lam0 lam2 M βhat μhat) :
    (Real.sqrt (lam0 / lam2) ≤ M →
      h1 X y lam0 lam2 M (L0BnB.Duality.alphaStar X y βs) (L0BnB.Duality.gammaStar X y lam2 M βs)
          - 2 * primalGap X βs βhat - (1 / 2) * primalGap X βs βhat ^ 2
          - ∑ i ∈ supp βhat,
              (cLemma2 lam2 M βs i * primalGap X βs βhat + (4 * lam2)⁻¹ * primalGap X βs βhat ^ 2)
        ≤ h1 X y lam0 lam2 M (alphaHat X y βhat) γhat) ∧
    (M < Real.sqrt (lam0 / lam2) →
      L0BnB.Duality.h2 y M (L0BnB.Duality.rhoStar X y βs) (L0BnB.Duality.muStar X y lam0 lam2 M βs)
          - primalGap X βs βhat * (2 + M * ((supp βhat).card : ℝ)) - primalGap X βs βhat ^ 2 / 2
        ≤ L0BnB.Duality.h2 y M (rhoHat X y βhat) μhat) := by sorry

end L0BnB.DualGap
