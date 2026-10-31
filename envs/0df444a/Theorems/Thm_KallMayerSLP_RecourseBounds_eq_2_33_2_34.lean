-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_eq_2_33_2_34
-- name    : KallMayerSLP.RecourseBounds.eq_2_33_2_34
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:48.707996+00:00
-- url     : https://prove2.me/theorems/9a6d6b2f-88ef-4100-bac2-339ad27d8663
-- title:
--   (2.33)–(2.34) — $\mathbb Q$ preserves all joint moments of $\mathbb P_\xi$
-- statement:
--   Let $\operatorname{supp}\mathbb P_\xi\subset\Xi=\times_{i=1}^r[\alpha_i,\beta_i]$. For $\Lambda\subset\{1,\dots,r\}$ let $h_\Lambda(\xi)=\prod_{k\in\Lambda}\xi_k$ (with $h_\emptyset=1$) and $\mu_\Lambda=\int_\Xi h_\Lambda(\xi)\,\mathbb P_\xi(d\xi)$. Then
--
--   1. (2.33) for every $\xi\in\Xi$, $\displaystyle\sum_{\nu=1}^{2^r}h_\Lambda(v^\nu)\,\mathbb P_{\eta(\xi)}(v^\nu)=h_\Lambda(\xi)$;
--   2. (2.34) the generalized E–M distribution preserves every joint moment:
--   $$
--   \sum_{\nu=1}^{2^r}h_\Lambda(v^\nu)\,\mathbb Q(v^\nu)=\mu_\Lambda\qquad\text{for all }\Lambda\subset\{1,\dots,r\}.
--   $$
--
--   So $\mathbb Q$ is feasible for the moment problem (2.35) with the joint moments of $\mathbb P_\xi$ as constraints.
--
--   **Formalization Note** $\Lambda$ ranges over `Finset (Fin r)` (0-based indices).
--
--   Differences from the source:
--   - encoding: random vector ξ with distribution IP_ξ, supp IP_ξ ⊂ Ξ = ×ᵢ[αᵢ, βᵢ] → probability measure P on Fin r → ℝ with P(Ξᶜ) = 0, Ξ = Set.Icc α β; reason: every quantity depends only on the law of ξ; Ξ is closed, so supp IP_ξ ⊂ Ξ is P(Ξᶜ) = 0; ℝ^r is Fin r → ℝ (0-based index)
--   - generalization: (2.26)/(2.30) divide by βᵢ − αᵢ, so the book's boxes have αᵢ < βᵢ → αᵢ = βᵢ allowed: a degenerate coordinate gets the point mass at its single value (vertexProb); reason: for αᵢ < βᵢ vertexProb is exactly the book's product of two-point laws, so the statement specializes to the book's
--   - encoding: (2.33) ∫_Ξ h_Λ(η) IP_{η(ξ)}(dη) = h_Λ(ξ) = Σ_ν h_Λ(v^ν) IP_{η(ξ)}(v^ν) → Σ_v h_Λ(boxVertex α β v) * vertexProb α β ξ v = h_Λ(ξ) for ξ ∈ Ξ; reason: the integral against the discrete law IP_{η(ξ)} is the vertex sum
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (2.33)–(2.34), p.217 (PDF 226)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMWeight

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, (2.33)–(2.34) — `Q` preserves all joint moments of `IP_ξ`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.33)–(2.34), printed p.217
(PDF 226): "For any `Λ ⊂ {1, ···, r}` define `h_Λ(ξ) := ∏_{k∈Λ} ξₖ` and denote the joint moments
for all `Λ ⊂ {1, ···, r}` as `m_Λ := ∫_Ξ h_Λ(ξ) IP_ξ(dξ)` (with `m_∅ = 1`). […] from (2.27) and (2.28)
follows `∫_Ξ h_Λ(η) IP_{η(ξ)}(dη) = h_Λ(ξ) = Σ_{ν=1}^{2^r} h_Λ(v^ν) · IP_{η(ξ)}(v^ν)`, (2.33) such that
(2.30) and (2.33) imply `Σ_{ν=1}^{2^r} h_Λ(v^ν) Q(v^ν) = ∫_Ξ Σ_ν h_Λ(v^ν) IP_{η(ξ)}(v^ν) IP_ξ(dξ)
= ∫_Ξ h_Λ(ξ) IP_ξ(dξ) = μ_Λ`. (2.34) Hence the upper bound distribution `Q` of Lemma 2.7 preserves all
joint moments of the original distribution `IP_ξ`."

**Formalization Note.** `IP_ξ` is a probability measure `P` on `Fin r → ℝ` with `P(Ξᶜ) = 0`,
`Λ` ranges over all `Finset (Fin r)` (the empty product is `1`), `IP_{η(ξ)}(v)` is
`vertexProb α β ξ v`, `Q(v)` is `genEMWeight P α β v`, and the vertex `v^ν` is
`NumStochOpt.Bounds.boxVertex α β v`. (2.33) is stated at every `ξ ∈ Ξ`. -/
theorem eq_2_33_2_34 {r : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hsupp : P (Set.Icc α β)ᶜ = 0) :
    (∀ Λ : Finset (Fin r), ∀ ξ ∈ Set.Icc α β,
      ∑ v : Fin r → Bool, (∏ k ∈ Λ, NumStochOpt.Bounds.boxVertex α β v k) * vertexProb α β ξ v =
        ∏ k ∈ Λ, ξ k) ∧
    ∀ Λ : Finset (Fin r),
      ∑ v : Fin r → Bool, (∏ k ∈ Λ, NumStochOpt.Bounds.boxVertex α β v k) * genEMWeight P α β v =
        ∫ ξ, ∏ k ∈ Λ, ξ k ∂P := by sorry

end KallMayerSLP.RecourseBounds
