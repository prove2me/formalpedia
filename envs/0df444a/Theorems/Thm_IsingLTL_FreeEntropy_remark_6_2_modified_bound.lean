-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_remark_6_2_modified_bound
-- name    : IsingLTL.FreeEntropy.remark_6_2_modified_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:30.724252+00:00
-- url     : https://prove2.me/theorems/4a4c293e-90e1-4ee5-8f74-45eb7b628f76
-- title:
--   Remark 6.2 — the bound (6.4) with $F_1$ replaced by $\tfrac12F_1(x,y)$ and constant $c\,\mathbb E[L^2]$
-- statement:
--   In the setting of Lemma 6.1, replace $F_1:\mathcal K\to\mathbb R$ by $\tfrac12F_1(x,y)$ for a twice differentiable symmetric function $F_1:\mathcal K^2\to\mathbb R$ (also with $|\partial^2F_1/\partial x_1\partial x_2|\le2c$). With $P_\ell=\mathbb P(L=\ell)$, the contribution of $L=1$ to the left-hand side of (6.1) is then $P_1\mathbb E[\partial_{x_1}F_1(x,X_2)]$, so the first-order condition reads
--   $$P_1\,\mathbb E[\partial_{x_1}F_1(x,X_2)]+\sum_{\ell\ge2}\ell P_\ell\,\mathbb E[\partial_{x_1}F_\ell(x,X_2,\dots,X_\ell)]=0\qquad\forall x\in\mathcal K,$$
--   and the bound (6.2) becomes
--   $$\Big|\frac{P_1}{2}\mathbb E[F_1(Y_1,Y_2)-F_1(X_1,X_2)]+\sum_{\ell\ge2}P_\ell\,\mathbb E[F_\ell(Y_1,\dots,Y_\ell)-F_\ell(X_1,\dots,X_\ell)]\Big|\le c\,\mathbb E[L^2]\,\|X-Y\|^2_{\mathrm{MK}}.$$
--
--   This is the form in which the lemma is applied to the Bethe functional.
--
--   **Formalization Note** The regularity, integrability and finite-distance conventions are those of Lemma 6.1; the uniform bound on $\ell^{-1}\mathbb E|\partial_{x_1}F_\ell|$ is required for $\ell\ge2$ and the bound on $\mathbb E|\partial_{x_1}F_1(x,X_2)|$ for $F_1$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 23, Remark 6.2, (6.4)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_MKDist
import Definitions.Def_IsingLTL_FreeEntropy_CoordDeriv

namespace IsingLTL.FreeEntropy

open MeasureTheory

/-- **Remark 6.2** (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*, arXiv:0804.4726v3,
p. 23, eq. (6.4)). In Lemma 6.1, replace `F₁ : K → ℝ` by `0.5 F₁(x, y)` for a twice
differentiable symmetric function `F₁ : K² → ℝ`. With `P_ℓ = P(L = ℓ)`, the contribution of
`L = 1` to the left-hand side of (6.1) is then `P₁ E[∂_{x₁}F₁(x, X₂)]`, and the bound (6.2)
becomes
`|(P₁/2) E[F₁(Y₁, Y₂) − F₁(X₁, X₂)] + ∑_{ℓ≥2} P_ℓ E[F_ℓ(Y₁, …, Y_ℓ) − F_ℓ(X₁, …, X_ℓ)]|
  ≤ c E[L²] ‖X − Y‖²_MK` (6.4).

Formalization Note. The hypotheses are those of Lemma 6.1 (see its note: laws `μX`, `μY` on `K`,
`L ∼ p` square integrable, `C²` on an open neighbourhood of `K^ℓ`, integrability of the functions
and of their first partial derivatives, finite MK distance) for the family `F₁` (on `K²`) and
`F_ℓ`, `ℓ ≥ 2`; `F_0` is constant and does not contribute. The bound `|∂²/∂x₁∂x₂| ≤ 2c` is
required of `F₁` and of every `F_ℓ`, `ℓ ≥ 2`; the uniform bound on `ℓ^{−1}E|∂_{x₁}F_ℓ(x, X₂, …)|`
is required for `ℓ ≥ 2` and for `E|∂_{x₁}F₁(x, X₂)|`. Condition (6.1) reads
`P₁ E[∂_{x₁}F₁(x, X₂)] + ∑_{ℓ≥2} ℓ P_ℓ E[∂_{x₁}F_ℓ(x, X₂, …, X_ℓ)] = 0` for all `x ∈ K`. The index
`m` of the series stands for `ℓ = m + 2`. Summability of the series in (6.4) is part of the
conclusion; `E[L²] = ∑_ℓ ℓ² p_ℓ`. -/
theorem remark_6_2_modified_bound (K : Set ℝ) (hK : Convex ℝ K)
    (F₁ : (Fin 2 → ℝ) → ℝ) (F : (ℓ : ℕ) → (Fin ℓ → ℝ) → ℝ)
    (hsymm₁ : ∀ (σ : Equiv.Perm (Fin 2)) (x : Fin 2 → ℝ), F₁ (x ∘ σ) = F₁ x)
    (hsymm : ∀ (m : ℕ) (σ : Equiv.Perm (Fin (m + 2))) (x : Fin (m + 2) → ℝ),
      F (m + 2) (x ∘ σ) = F (m + 2) x)
    (hC2₁ : ∃ U : Set (Fin 2 → ℝ), IsOpen U ∧ Set.pi Set.univ (fun _ => K) ⊆ U ∧
      ContDiffOn ℝ 2 F₁ U)
    (hC2 : ∀ m : ℕ, ∃ U : Set (Fin (m + 2) → ℝ), IsOpen U ∧ Set.pi Set.univ (fun _ => K) ⊆ U ∧
      ContDiffOn ℝ 2 (F (m + 2)) U)
    (c : ℝ)
    (hc₁ : ∀ x : Fin 2 → ℝ, x ∈ Set.pi Set.univ (fun _ => K) →
      |coordDeriv (fun y => coordDeriv F₁ 1 y) 0 x| ≤ 2 * c)
    (hc : ∀ (m : ℕ) (x : Fin (m + 2) → ℝ), x ∈ Set.pi Set.univ (fun _ => K) →
      |coordDeriv (fun y => coordDeriv (F (m + 2)) 1 y) 0 x| ≤ 2 * c)
    (μX μY : ProbabilityMeasure ℝ)
    (hXK : ∀ᵐ x ∂(μX : Measure ℝ), x ∈ K) (hYK : ∀ᵐ y ∂(μY : Measure ℝ), y ∈ K)
    (hdint₁ : ∀ x : ℝ, x ∈ K →
      Integrable (fun z : Fin 1 → ℝ => coordDeriv F₁ 0 (Fin.cons x z : Fin 2 → ℝ))
        (Measure.pi fun _ => (μX : Measure ℝ)))
    (hdint : ∀ (m : ℕ) (x : ℝ), x ∈ K →
      Integrable (fun z : Fin (m + 1) → ℝ => coordDeriv (F (m + 2)) 0 (Fin.cons x z : Fin (m + 2) → ℝ))
        (Measure.pi fun _ => (μX : Measure ℝ)))
    (hdbdd : ∃ Cd : ℝ, (∀ x : ℝ, x ∈ K →
        ∫ z : Fin 1 → ℝ, |coordDeriv F₁ 0 (Fin.cons x z : Fin 2 → ℝ)|
          ∂(Measure.pi fun _ => (μX : Measure ℝ)) ≤ Cd) ∧
      ∀ (m : ℕ) (x : ℝ), x ∈ K →
        (1 / ((m : ℝ) + 2)) * ∫ z : Fin (m + 1) → ℝ,
          |coordDeriv (F (m + 2)) 0 (Fin.cons x z : Fin (m + 2) → ℝ)|
            ∂(Measure.pi fun _ => (μX : Measure ℝ)) ≤ Cd)
    (p : ℕ → ℝ) (hp0 : ∀ ℓ, 0 ≤ p ℓ) (hp1 : HasSum p 1)
    (hp2 : Summable (fun ℓ : ℕ => (ℓ : ℝ) ^ 2 * p ℓ))
    (h61 : ∀ x ∈ K,
      p 1 * ∫ z : Fin 1 → ℝ, coordDeriv F₁ 0 (Fin.cons x z : Fin 2 → ℝ)
          ∂(Measure.pi fun _ => (μX : Measure ℝ)) +
        ∑' m : ℕ, p (m + 2) * (((m : ℝ) + 2) * ∫ z : Fin (m + 1) → ℝ,
          coordDeriv (F (m + 2)) 0 (Fin.cons x z : Fin (m + 2) → ℝ)
            ∂(Measure.pi fun _ => (μX : Measure ℝ))) = 0)
    (hF₁X : Integrable F₁ (Measure.pi fun _ : Fin 2 => (μX : Measure ℝ)))
    (hF₁Y : Integrable F₁ (Measure.pi fun _ : Fin 2 => (μY : Measure ℝ)))
    (hFX : ∀ m : ℕ, Integrable (F (m + 2)) (Measure.pi fun _ : Fin (m + 2) => (μX : Measure ℝ)))
    (hFY : ∀ m : ℕ, Integrable (F (m + 2)) (Measure.pi fun _ : Fin (m + 2) => (μY : Measure ℝ)))
    (hMK : mkDist μX μY ≠ ⊤) :
    Summable (fun m : ℕ => p (m + 2) *
        ((∫ y, F (m + 2) y ∂(Measure.pi fun _ => (μY : Measure ℝ))) -
          ∫ x, F (m + 2) x ∂(Measure.pi fun _ => (μX : Measure ℝ)))) ∧
      |p 1 / 2 * ((∫ y, F₁ y ∂(Measure.pi fun _ => (μY : Measure ℝ))) -
            ∫ x, F₁ x ∂(Measure.pi fun _ => (μX : Measure ℝ))) +
          ∑' m : ℕ, p (m + 2) *
            ((∫ y, F (m + 2) y ∂(Measure.pi fun _ => (μY : Measure ℝ))) -
              ∫ x, F (m + 2) x ∂(Measure.pi fun _ => (μX : Measure ℝ)))| ≤
        c * (∑' ℓ : ℕ, (ℓ : ℝ) ^ 2 * p ℓ) * (mkDist μX μY).toReal ^ 2 := by sorry

end IsingLTL.FreeEntropy
