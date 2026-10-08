-- Prove2me | Theorems.Thm_OTDRO_WorstCase_dual_lambda_derivatives
-- name    : OTDRO.WorstCase.dual_lambda_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:19.402192+00:00
-- url     : https://prove2.me/theorems/ca17cb4a-764a-4a0b-8e59-525ed02c26df
-- title:
--   Proof of Theorem 6(c), p. 39 — on 𝕌₁, ∂±f_δ/∂λ = √δ(1 − E[βᵀA(X)⁻¹β inf/sup_{g∈Γ*} g²])
-- statement:
--   Assume Assumptions 1 and 2, $\delta>0$, $B\subseteq\mathbb R^d$ convex, and fix $\beta\in B$ with $\beta\neq0$. Then $f_\delta(\beta,\lambda)$ is finite for every $\lambda>\lambda_{thr}(\beta)$, and for every such $\lambda$: for $P_0$-almost every $x$ the set $\Gamma^*(\beta,\lambda;x)$ is nonempty and $\{g^2:g\in\Gamma^*(\beta,\lambda;x)\}$ is bounded, the functions $x\mapsto\beta^{\mathsf T}A(x)^{-1}\beta\inf_{g\in\Gamma^*}g^2$ and $x\mapsto\beta^{\mathsf T}A(x)^{-1}\beta\sup_{g\in\Gamma^*}g^2$ are $P_0$-integrable, and the right and left derivatives of $\lambda\mapsto f_\delta(\beta,\lambda)$ are
--   $$\frac{\partial_+f_\delta}{\partial\lambda}(\beta,\lambda)=\sqrt\delta\Bigl(1-E_{P_0}\Bigl[\beta^{\mathsf T}A(X)^{-1}\beta\inf_{g\in\Gamma^*(\beta,\lambda;X)}g^2\Bigr]\Bigr),\qquad \frac{\partial_-f_\delta}{\partial\lambda}(\beta,\lambda)=\sqrt\delta\Bigl(1-E_{P_0}\Bigl[\beta^{\mathsf T}A(X)^{-1}\beta\sup_{g\in\Gamma^*(\beta,\lambda;X)}g^2\Bigr]\Bigr).$$
--
--   At a dual optimizer $\lambda_*(\beta)>\lambda_{thr}(\beta)$ the first-order conditions $\partial_+f_\delta\ge0\ge\partial_-f_\delta$ turn these formulas into $\underline c\le1\le\bar c$, which is what lets the randomized worst case of Theorem 6(c) spend exactly the budget $\delta$.
--
--   **Formalization Note** This is an unnumbered display in the proof of Theorem 6(c), which the page derives from Proposition 2 and a general result on directional derivatives of integral functionals ([2, Proposition 2.1]); it is stated here under Assumptions 1–2 only, without Proposition 2's max-of-$C^1$ form, which is what the proof of Theorem 6 uses. $\beta\neq0$ is the hypothesis of Theorem 6, in whose proof the display appears; at $\beta=0$, $\Gamma^*=\mathbb R$ and $\sup g^2=\infty$. Finiteness of $f_\delta$ (neither $+\infty$ nor $-\infty$) on $\{\lambda>\lambda_{thr}(\beta)\}$ is a conjunct, so the derivatives of $\lambda\mapsto f_\delta(\beta,\lambda)$ are taken of its real values. Infimum and supremum over $\Gamma^*$ are real `sInf`/`sSup` of $\{g^2\}$; nonemptiness and boundedness are conjuncts, and integrability is a conjunct so that the expectations are genuine.
-- source:
--   arXiv:1810.02403v3, §5.4, proof of Theorem 6(c), p. 39

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

open MeasureTheory

namespace OTDRO.WorstCase

/-- **One-sided `λ`-derivatives of `f_δ` on `𝕌₁`** (arXiv:1810.02403v3, §5.4, proof of
Theorem 6(c), p. 39; unnumbered). Under Assumptions 1–2, for `β ∈ B`, `β ≠ 0`: `f_δ(β, λ)` is
finite for `λ > λ_thr(β)`, and at every such `λ`
`∂₊f_δ/∂λ(β, λ) = √δ(1 − E[βᵀA(X)⁻¹β inf_{g∈Γ*(β,λ;X)} g²])`,
`∂₋f_δ/∂λ(β, λ) = √δ(1 − E[βᵀA(X)⁻¹β sup_{g∈Γ*(β,λ;X)} g²])`. -/
theorem dual_lambda_derivatives {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0) :
    (∀ l : ℝ, OTDRO.Dual.lamThr P0 ℓ A δ β < l → OTDRO.Dual.fDelta P0 ℓ A δ β l ≠ ⊤ ∧ OTDRO.Dual.fDelta P0 ℓ A δ β l ≠ ⊥) ∧
    ∀ lam : ℝ, OTDRO.Dual.lamThr P0 ℓ A δ β < lam →
      (∀ᵐ x ∂P0, (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty ∧
        BddAbove ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x)) ∧
      Integrable (fun x => OTDRO.Dual.quadInv A β x *
        sInf ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x)) P0 ∧
      Integrable (fun x => OTDRO.Dual.quadInv A β x *
        sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x)) P0 ∧
      HasDerivWithinAt (fun l => (OTDRO.Dual.fDelta P0 ℓ A δ β l).toReal)
        (Real.sqrt δ * (1 - ∫ x, OTDRO.Dual.quadInv A β x *
          sInf ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x) ∂P0))
        (Set.Ici lam) lam ∧
      HasDerivWithinAt (fun l => (OTDRO.Dual.fDelta P0 ℓ A δ β l).toReal)
        (Real.sqrt δ * (1 - ∫ x, OTDRO.Dual.quadInv A β x *
          sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam x) ∂P0))
        (Set.Iic lam) lam := by sorry

end OTDRO.WorstCase
