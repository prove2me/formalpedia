-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_lemma_6_1_second_order
-- name    : IsingLTL.FreeEntropy.lemma_6_1_second_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:28.514352+00:00
-- url     : https://prove2.me/theorems/944bff93-3a57-4d1e-a9f8-a3087d2415b5
-- title:
--   Lemma 6.1 — second-order stability $|\mathbb E[F_L(Y)-F_L(X)]|\le c\,\mathbb E[L(L-1)]\|X-Y\|^2_{\mathrm{MK}}$
-- statement:
--   Let $\mathcal K\subseteq\mathbb R$ be convex and $F_\ell:\mathcal K^\ell\to\mathbb R$ symmetric, twice differentiable functions ($F_0$ constant) with
--   $$\sup_\ell\sup_{\mathcal K^\ell}\Big|\frac{\partial^2F_\ell}{\partial x_1\partial x_2}\Big|\le2c.$$
--   Let $X,X_i$ be i.i.d. in $\mathcal K$ such that $\ell^{-1}\mathbb E|\partial_{x_1}F_\ell(x,X_2,\dots,X_\ell)|$ is bounded uniformly in $\ell$ and $x\in\mathcal K$, and let $L$ be an independent, square-integrable, nonnegative integer valued random variable with
--   $$\mathbb E[L\,\partial_{x_1}F_L(x,X_2,\dots,X_L)]=0\qquad\forall x\in\mathcal K.$$
--   Then for any i.i.d. $Y,Y_i\in\mathcal K$ independent of $L$,
--   $$\big|\mathbb E[F_L(Y_1,\dots,Y_L)-F_L(X_1,\dots,X_L)]\big|\le c\,\mathbb E[L(L-1)]\,\|X-Y\|^2_{\mathrm{MK}}.$$
--
--   The vanishing first-order condition turns a first-order perturbation estimate into a quadratic one.
--
--   **Formalization Note**
--   1. "Twice differentiable" is taken as $C^2$ on an open neighbourhood of $\mathcal K^\ell$; the mixed-derivative bound is required for $\ell\ge2$.
--   2. Integrability of $\partial_{x_1}F_\ell(x,X_2,\dots)$ and of $F_\ell$ under the product laws of the $X_i$ and of the $Y_i$ is assumed, so that no expectation is a junk value; summability of the series over $L$ in the conclusion is asserted.
--   3. The case $\|X-Y\|_{\mathrm{MK}}=\infty$, which the paper notes is trivial, is excluded.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, pp. 21-22, Lemma 6.1, (6.1)-(6.2)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_MKDist
import Definitions.Def_IsingLTL_FreeEntropy_CoordDeriv

namespace IsingLTL.FreeEntropy

open MeasureTheory

/-- **Lemma 6.1** (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*, arXiv:0804.4726v3,
pp. 21–22, eq. (6.2)). Consider a convex set `K ⊆ ℝ` and symmetric twice differentiable functions
`F_ℓ : K^ℓ → ℝ` with `F_0` constant, such that for some finite constant `c`,
`sup_ℓ sup_{K^ℓ} |∂²F_ℓ/∂x₁∂x₂| ≤ 2c`. Suppose i.i.d. `X, X_i ∈ K` are such that
`ℓ^{−1} E|∂_{x₁}F_ℓ(x, X₂, …, X_ℓ)|` is bounded uniformly in `ℓ` and `x ∈ K`, and the independent,
square-integrable, nonnegative integer valued random variable `L` satisfies
`E[L ∂_{x₁}F_L(x, X₂, …, X_L)] = 0` for all `x ∈ K` (6.1). Then, for any i.i.d. `Y, Y_i ∈ K`
also independent of `L`,
`|E[F_L(Y₁, …, Y_L) − F_L(X₁, …, X_L)]| ≤ c E[L(L − 1)] ‖X − Y‖²_MK` (6.2).

Formalization Note.
1. `L` has law `p` on `ℕ` (`p ℓ = P(L = ℓ)`, `∑ ℓ² p_ℓ < ∞`); `X` and `Y` have laws `μX`, `μY`
   concentrated on `K`; an expectation over `L` and i.i.d. copies is `∑_ℓ p_ℓ ∫ … d(μ^{⊗ℓ})`.
   Coordinates `x₁, x₂` are indices `0, 1`; `(x, X₂, …, X_ℓ)` is `Fin.cons x z` with `z ∼ μX^{⊗(ℓ−1)}`.
2. "Twice differentiable on `K^ℓ`" is taken as `C²` on an open neighbourhood of `K^ℓ` (`K` may
   have empty interior or contain endpoints). `F_0` is automatically constant.
3. The bound on `∂²F_ℓ/∂x₁∂x₂` is required for `ℓ ≥ 2` (the only `ℓ` with a coordinate `x₂`).
4. Integrability of `∂_{x₁}F_ℓ(x, X₂, …)` and of `F_ℓ` under `μX^{⊗ℓ}` and `μY^{⊗ℓ}` is assumed, so
   that the expectations in the hypotheses and in (6.2) are not junk values; the series in (6.1)
   is then absolutely summable by the uniform bound and `E[L²] < ∞`. Summability of the series in
   (6.2) is part of the conclusion.
5. The case `‖X − Y‖_MK = ∞`, in which the paper notes the bound is trivial, is excluded; the
   distance is then a real number. -/
theorem lemma_6_1_second_order (K : Set ℝ) (hK : Convex ℝ K)
    (F : (ℓ : ℕ) → (Fin ℓ → ℝ) → ℝ)
    (hsymm : ∀ (ℓ : ℕ) (σ : Equiv.Perm (Fin ℓ)) (x : Fin ℓ → ℝ), F ℓ (x ∘ σ) = F ℓ x)
    (hC2 : ∀ ℓ : ℕ, ∃ U : Set (Fin ℓ → ℝ), IsOpen U ∧ Set.pi Set.univ (fun _ => K) ⊆ U ∧
      ContDiffOn ℝ 2 (F ℓ) U)
    (c : ℝ)
    (hc : ∀ (ℓ : ℕ) (h2 : 2 ≤ ℓ) (x : Fin ℓ → ℝ), x ∈ Set.pi Set.univ (fun _ => K) →
      |coordDeriv (fun y => coordDeriv (F ℓ) ⟨1, h2⟩ y) ⟨0, by omega⟩ x| ≤ 2 * c)
    (μX μY : ProbabilityMeasure ℝ)
    (hXK : ∀ᵐ x ∂(μX : Measure ℝ), x ∈ K) (hYK : ∀ᵐ y ∂(μY : Measure ℝ), y ∈ K)
    (hdint : ∀ (m : ℕ) (x : ℝ), x ∈ K →
      Integrable (fun z : Fin m → ℝ => coordDeriv (F (m + 1)) 0 (Fin.cons x z : Fin (m + 1) → ℝ))
        (Measure.pi fun _ => (μX : Measure ℝ)))
    (hdbdd : ∃ Cd : ℝ, ∀ (m : ℕ) (x : ℝ), x ∈ K →
      (1 / ((m : ℝ) + 1)) * ∫ z : Fin m → ℝ,
        |coordDeriv (F (m + 1)) 0 (Fin.cons x z : Fin (m + 1) → ℝ)|
          ∂(Measure.pi fun _ => (μX : Measure ℝ)) ≤ Cd)
    (p : ℕ → ℝ) (hp0 : ∀ ℓ, 0 ≤ p ℓ) (hp1 : HasSum p 1)
    (hp2 : Summable (fun ℓ : ℕ => (ℓ : ℝ) ^ 2 * p ℓ))
    (h61 : ∀ x ∈ K, ∑' m : ℕ, p (m + 1) * (((m : ℝ) + 1) * ∫ z : Fin m → ℝ,
        coordDeriv (F (m + 1)) 0 (Fin.cons x z : Fin (m + 1) → ℝ)
          ∂(Measure.pi fun _ => (μX : Measure ℝ))) = 0)
    (hFX : ∀ ℓ : ℕ, Integrable (F ℓ) (Measure.pi fun _ : Fin ℓ => (μX : Measure ℝ)))
    (hFY : ∀ ℓ : ℕ, Integrable (F ℓ) (Measure.pi fun _ : Fin ℓ => (μY : Measure ℝ)))
    (hMK : mkDist μX μY ≠ ⊤) :
    Summable (fun ℓ : ℕ => p ℓ *
        ((∫ y, F ℓ y ∂(Measure.pi fun _ => (μY : Measure ℝ))) -
          ∫ x, F ℓ x ∂(Measure.pi fun _ => (μX : Measure ℝ)))) ∧
      |∑' ℓ : ℕ, p ℓ *
          ((∫ y, F ℓ y ∂(Measure.pi fun _ => (μY : Measure ℝ))) -
            ∫ x, F ℓ x ∂(Measure.pi fun _ => (μX : Measure ℝ)))| ≤
        c * (∑' ℓ : ℕ, (ℓ : ℝ) * ((ℓ : ℝ) - 1) * p ℓ) * (mkDist μX μY).toReal ^ 2 := by sorry

end IsingLTL.FreeEntropy
