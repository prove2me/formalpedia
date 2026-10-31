-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_lemma_2_7
-- name    : KallMayerSLP.RecourseBounds.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:24.624894+00:00
-- url     : https://prove2.me/theorems/91474264-c3cd-4fdc-aaf4-610e7bfcd24d
-- title:
--   Lemma 2.7 — the generalized Edmundson–Madansky inequality
-- statement:
--   Let $\operatorname{supp}\mathbb P_\xi\subset\Xi=\times_{i=1}^r[\alpha_i,\beta_i]$, with the components of $\xi$ possibly dependent, and let $\varphi:\Xi\to\mathbb R$ be convex. Then:
--
--   1. (2.29) for every $\xi\in\Xi$, $\varphi(\xi)\le\sum_{\nu=1}^{2^r}\varphi(v^\nu)\,\mathbb P_{\eta(\xi)}(v^\nu)$, where $\mathbb P_{\eta(\xi)}$ is the vertex law (2.28) with mean $\xi$;
--   2. the generalized E–M distribution $\mathbb Q(v^\nu)=\int_\Xi\mathbb P_{\eta(\xi)}(v^\nu)\,\mathbb P_\xi(d\xi)$ of (2.30) is a probability on the vertices: $\mathbb Q(v^\nu)\ge0$ and $\sum_\nu\mathbb Q(v^\nu)=1$;
--   3. (2.31) the generalized E–M inequality holds:
--   $$
--   \mathbb E_\xi[\varphi(\xi)]\le\sum_{\nu=1}^{2^r}\varphi(v^\nu)\,\mathbb Q(v^\nu).
--   $$
--
--   Unlike the product bound of Lemma 2.6, this upper bound holds for arbitrary dependence between the components.
--
--   **Formalization Note** $\mathbb P_{\eta(\xi)}(v)$ is `vertexProb`, $\mathbb Q(v)$ is `genEMWeight`, and the right side of (2.31) is `genEMBound`.
--
--   Differences from the source:
--   - encoding: random vector ξ with distribution IP_ξ, supp IP_ξ ⊂ Ξ = ×ᵢ[αᵢ, βᵢ] → probability measure P on Fin r → ℝ with P(Ξᶜ) = 0, Ξ = Set.Icc α β; reason: every quantity depends only on the law of ξ; Ξ is closed, so supp IP_ξ ⊂ Ξ is P(Ξᶜ) = 0; ℝ^r is Fin r → ℝ (0-based index)
--   - encoding: φ : Ξ → ℝ convex → φ : (Fin r → ℝ) → ℝ with ConvexOn ℝ (Set.Icc α β) φ; reason: values outside Ξ never enter the statement
--   - generalization: (2.26)/(2.30) divide by βᵢ − αᵢ, so the book's boxes have αᵢ < βᵢ → αᵢ = βᵢ allowed: a degenerate coordinate gets the point mass at its single value (vertexProb); reason: for αᵢ < βᵢ vertexProb is exactly the book's product of two-point laws, so the statement specializes to the book's
--   - encoding: (2.29) φ(ξ) ≤ ∫_Ξ φ(η(ξ)) IP_{η(ξ)}(dη) = Σ_ν φ(v^ν) IP_{η(ξ)}(v^ν) → ∀ ξ ∈ Ξ, φ ξ ≤ Σ_v vertexProb α β ξ v * φ(boxVertex α β v); reason: the book's integral is the vertex sum, as the book's own second line says
--   - encoding: 'the probability measure Q' → conjuncts ∀ v, 0 ≤ Q v and Σ_v Q v = 1; reason: what it means for Q to be a probability on the finitely many vertices
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Lemma 2.7, (2.29)–(2.31), p.216 (PDF 225)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMBound

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, Lemma 2.7 — the generalized Edmundson–Madansky inequality.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.7, (2.29)–(2.31), printed
p.216 (PDF 225): "For any convex function `φ : Ξ → ℝ`, Jensen's inequality implies
`φ(IE_ζ[ζ]) = φ(ξ) ≤ ∫_Ξ φ(η(ξ)) IP_{η(ξ)}(dη) = Σ_{ν=1}^{2^r} φ(v^ν) IP_{η(ξ)}(v^ν)`. (2.29)
Hence, with the probability measure `Q` defined on the vertices `v^ν` of `Ξ` by
`Q(v^ν) = ∫_Ξ IP_{η(ξ)}(v^ν) IP_ξ(dξ)` (2.30) we get the generalized E–M inequality
`IE_ξ[φ(ξ)] ≤ Σ_{ν=1}^{2^r} φ(v^ν) Q(v^ν)`. (2.31)"
Setting (p.215): `supp IP_ξ ⊂ Ξ = ×_{i=1}^r [αᵢ, βᵢ]`, components of `ξ` possibly dependent.

The statement has four parts: (2.29) at every `ξ ∈ Ξ`; `Q` is a probability on the vertices
(nonnegative, total mass `1`); and (2.31).

**Formalization Note.** `IP_ξ` is a probability measure `P` on `Fin r → ℝ` with `P(Ξᶜ) = 0`;
`IP_{η(ξ)}(v)` is `vertexProb α β ξ v`, `Q(v)` is `genEMWeight P α β v`, and the right side of (2.31)
is `genEMBound P α β φ`. A degenerate coordinate `αᵢ = βᵢ` is allowed (the vertex law puts its mass
on the single value). No integrability hypothesis: a function convex on a box is bounded and Borel
on it. -/
theorem lemma_2_7 {r : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (φ : (Fin r → ℝ) → ℝ) (hφ : ConvexOn ℝ (Set.Icc α β) φ) :
    (∀ ξ ∈ Set.Icc α β,
      φ ξ ≤ ∑ v : Fin r → Bool, vertexProb α β ξ v * φ (NumStochOpt.Bounds.boxVertex α β v)) ∧
    (∀ v, 0 ≤ genEMWeight P α β v) ∧
    ∑ v : Fin r → Bool, genEMWeight P α β v = 1 ∧
    ∫ ξ, φ ξ ∂P ≤ genEMBound P α β φ := by sorry

end KallMayerSLP.RecourseBounds
