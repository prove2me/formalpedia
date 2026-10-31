-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_corollary_2_2
-- name    : KallMayerSLP.RecourseBounds.corollary_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:17.294109+00:00
-- url     : https://prove2.me/theorems/9261f9a5-f5d5-4001-aa41-d89407dae54d
-- title:
--   Corollary 2.2 — E–M inequality for separable convex integrands
-- statement:
--   Let $\xi$ be a random vector with $\operatorname{supp}\mathbb P_\xi\subset\Xi=\times_{i=1}^r[\alpha_i,\beta_i]$, $\alpha_i<\beta_i$, and mean $\mu=\mathbb E_\xi[\xi]$. Let $\varphi(\xi)=\sum_{i=1}^r\varphi_i(\xi_i)$ be convex and separable on $\Xi$, and let $\mathbb P_{\eta_i}$ be the two-point laws (2.19) on $\{\alpha_i,\beta_i\}$ with means $\mu_i$:
--   $$
--   \mathbb P_{\eta_i}(\alpha_i)=\frac{\beta_i-\mu_i}{\beta_i-\alpha_i},\qquad \mathbb P_{\eta_i}(\beta_i)=\frac{\mu_i-\alpha_i}{\beta_i-\alpha_i}.
--   $$
--   Then, with no independence assumption on the components of $\xi$,
--   $$
--   \mathbb E_\xi[\varphi(\xi)]=\sum_{i=1}^r\mathbb E_\xi[\varphi_i(\xi_i)]\le\sum_{i=1}^r\mathbb E_{\eta_i}[\varphi_i(\eta_i)] .
--   $$
--
--   For separable integrands the one-dimensional E–M bound therefore extends to dependent random vectors.
--
--   **Formalization Note** $\mathbb E_{\eta_i}[\varphi_i(\eta_i)]$ is written out as $\mathbb P_{\eta_i}(\alpha_i)\varphi_i(\alpha_i)+\mathbb P_{\eta_i}(\beta_i)\varphi_i(\beta_i)$ with the platform's `emProb`.
--
--   Differences from the source:
--   - encoding: random vector ξ with distribution IP_ξ, supp IP_ξ ⊂ Ξ = ×ᵢ[αᵢ, βᵢ] → probability measure P on Fin r → ℝ with P(Ξᶜ) = 0, Ξ = Set.Icc α β; reason: every quantity depends only on the law of ξ; Ξ is closed, so supp IP_ξ ⊂ Ξ is P(Ξᶜ) = 0; ℝ^r is Fin r → ℝ (0-based index)
--   - encoding: φ : Ξ → ℝ convex separable, φ(ξ) = Σᵢ φᵢ(ξᵢ) → φ : Fin r → ℝ → ℝ with ConvexOn ℝ (Set.Icc α β) (fun x => Σᵢ φ i (x i)); reason: the same condition; values outside Ξ never enter
--   - encoding: IE_{ηᵢ}[φᵢ(ηᵢ)] with IP_{ηᵢ} from (2.19) → emProb αᵢ βᵢ μᵢ false · φᵢ(αᵢ) + emProb αᵢ βᵢ μᵢ true · φᵢ(βᵢ); reason: the expectation of a two-point law written out
--   - encoding: the two-point laws (2.19) divide by βᵢ − αᵢ → hypothesis αᵢ < βᵢ for every i; reason: excludes exactly the boxes where (2.19) is undefined
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Corollary 2.2, (2.24), p.214 (PDF 223)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, Corollary 2.2 — the E–M inequality for separable convex integrands.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Corollary 2.2, (2.24), printed
p.214 (PDF 223): "Let `supp IP_ξ ⊂ Ξ = ×_{i=1}^r [αᵢ, βᵢ] ⊂ ℝ^r` with `μ = IE_ξ[ξ]` and assume the
function `φ : Ξ → ℝ` to be convex separable, i.e. `φ(ξ) = Σ_{i=1}^r φᵢ(ξᵢ)`. Then, with the
distributions `IP_{ηᵢ}` given in (2.19), it follows that
`IE_ξ[φ(ξ)] = Σ_{i=1}^r IE_ξ[φᵢ(ξᵢ)] ≤ Σ_{i=1}^r IE_{ηᵢ}[φᵢ(ηᵢ)]`."

**Formalization Note.** `IP_ξ` is a probability measure `P` on `Fin r → ℝ` with `P(Ξᶜ) = 0`
(`supp IP_ξ ⊂ Ξ` for the closed box `Ξ = Set.Icc α β`). `IE_{ηᵢ}[φᵢ(ηᵢ)]` is written out with the
two-point law (2.19): `emProb αᵢ βᵢ μᵢ false · φᵢ(αᵢ) + emProb αᵢ βᵢ μᵢ true · φᵢ(βᵢ)`, with
`emProb` the platform's `NumStochOpt.Bounds.emProb`. `αᵢ < βᵢ` is the nondegeneracy that (2.19)
divides by. No integrability hypothesis: a function convex on a box is bounded and Borel on it. -/
theorem corollary_2_2 {r : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hαβ : ∀ i, α i < β i) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (φ : Fin r → ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc α β) (fun x => ∑ i, φ i (x i))) :
    ∫ x, ∑ i, φ i (x i) ∂P = ∑ i, ∫ x, φ i (x i) ∂P ∧
    ∑ i, ∫ x, φ i (x i) ∂P ≤
      ∑ i, (NumStochOpt.Bounds.emProb (α i) (β i) (∫ x, x i ∂P) false * φ i (α i) +
        NumStochOpt.Bounds.emProb (α i) (β i) (∫ x, x i ∂P) true * φ i (β i)) := by sorry

end KallMayerSLP.RecourseBounds
