-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_moment_problem_solution
-- name    : KallMayerSLP.RecourseBounds.moment_problem_solution
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:48.346017+00:00
-- url     : https://prove2.me/theorems/2a21dd4d-177a-444d-b4e6-ad96ad76c76e
-- title:
--   (2.35), p.219 — the generalized E–M distribution solves the moment problem (corrected: uniqueness clause dropped)
-- statement:
--   Let $\operatorname{supp}\mathbb P_\xi\subset\Xi=\times_{i=1}^r[\alpha_i,\beta_i]$, let $\varphi:\Xi\to\mathbb R$ be convex, and let $\mu_\Lambda=\int h_\Lambda\,d\mathbb P_\xi$ be the joint moments, $h_\Lambda(\xi)=\prod_{k\in\Lambda}\xi_k$. Consider the moment problem (2.35) over the set $\mathcal P$ of probability measures on $\Xi$:
--   $$
--   \gamma(P)=\sup_{\mathbb P\in\mathcal P}\Big\{\int_\Xi\varphi(\xi)\,\mathbb P(d\xi)\ \Big|\ \int_\Xi h_\Lambda(\xi)\,\mathbb P(d\xi)=\mu_\Lambda\ \ \forall\Lambda\subset\{1,\dots,r\}\Big\}.
--   $$
--   The generalized E–M distribution $\mathbb Q=\sum_\nu\mathbb Q(v^\nu)\delta_{v^\nu}$ solves it:
--
--   1. $\mathbb Q$ is a probability measure carried by $\Xi$;
--   2. $\mathbb Q$ is feasible: $\int h_\Lambda\,d\mathbb Q=\mu_\Lambda$ for every $\Lambda$;
--   3. $\int\varphi\,d\mathbb Q=\sum_\nu\varphi(v^\nu)\,\mathbb Q(v^\nu)$;
--   4. every feasible $\mathbb P\in\mathcal P$ satisfies $\int\varphi\,d\mathbb P\le\int\varphi\,d\mathbb Q$.
--
--   This optimality is the step that makes the partitioned E–M bound (2.40) no larger than the global one.
--
--   **Formalization Note** Probability measures on $\Xi$ are probability measures on `Fin r → ℝ` that give $\Xi^c$ measure $0$; $\mathbb Q$ is `genEMMeasure`.
--
--   Differences from the source:
--   - encoding: random vector ξ with distribution IP_ξ, supp IP_ξ ⊂ Ξ = ×ᵢ[αᵢ, βᵢ] → probability measure P on Fin r → ℝ with P(Ξᶜ) = 0, Ξ = Set.Icc α β; reason: every quantity depends only on the law of ξ; Ξ is closed, so supp IP_ξ ⊂ Ξ is P(Ξᶜ) = 0; ℝ^r is Fin r → ℝ (0-based index)
--   - encoding: φ : Ξ → ℝ convex → φ : (Fin r → ℝ) → ℝ with ConvexOn ℝ (Set.Icc α β) φ; reason: values outside Ξ never enter the statement
--   - generalization: (2.26)/(2.30) divide by βᵢ − αᵢ, so the book's boxes have αᵢ < βᵢ → αᵢ = βᵢ allowed: a degenerate coordinate gets the point mass at its single value (vertexProb); reason: for αᵢ < βᵢ vertexProb is exactly the book's product of two-point laws, so the statement specializes to the book's
--   - encoding: 𝒫, the set of all probability measures on Ξ → probability measures P' on Fin r → ℝ with P'(Ξᶜ) = 0; reason: measures on Ξ and measures on ℝ^r carried by the closed set Ξ correspond
--   - encoding: Q solves the moment problem (P) → Q is feasible and ∫φ dP' ≤ ∫φ dQ for every feasible P'; reason: a solution is a feasible point attaining the supremum
--   - correction: 'and as shown in Kall [137], it is the unique solution of (P)' → uniqueness not stated; reason: false for affine φ: r = 1, Ξ = [0,1], IP_ξ = δ_{1/2}, φ ≡ 0; then Q = ½δ₀ + ½δ₁ and δ_{1/2} are both feasible and optimal, and they differ
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (2.35)–(2.37), pp.217–219 (PDF 226–228)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMBound
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMMeasure

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, (2.35), p.219 — the generalized E–M distribution solves the moment problem (P).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.35)–(2.37), printed pp.217–219
(PDF 226–228). The moment problem (2.35), for `𝒫` the set of all probability measures on `Ξ`:
"`γ(P) := sup_{IP∈𝒫} {∫_Ξ φ(ξ) IP(dξ) | ∫_Ξ h_Λ(ξ) IP(dξ) = μ_Λ ∀Λ ⊂ {1, ···, r}}`"; conclusion,
p.219: "Therefore we have `γ(P̃) ≥ γ(P) ⟹ γ(P̃) = γ(P)`, such that the generalized E–M distribution
`Q` solves the moment problem (P)". Here `φ` is the convex function of Lemma 2.7, `h_Λ(ξ) = ∏_{k∈Λ} ξₖ`
and `μ_Λ = ∫ h_Λ dIP_ξ`.

"`Q` solves (P)" is stated as: `Q` is a probability measure carried by `Ξ`, it is feasible (has the
joint moments `μ_Λ`), its objective value is `∫ φ dQ = Σ_ν φ(v^ν) Q(v^ν)`, and every feasible
probability measure `IP` on `Ξ` has `∫ φ dIP ≤ ∫ φ dQ`.

**Formalization Note.** `IP_ξ` is a probability measure `P` on `Fin r → ℝ` with `P(Ξᶜ) = 0`;
probability measures on `Ξ` are probability measures `P'` on `Fin r → ℝ` with `P'(Ξᶜ) = 0`. `Q` is
`genEMMeasure P α β`, the discrete measure with mass `Q(v)` at each vertex. The uniqueness claims
cited from Kall [137] are not part of this statement. -/
theorem moment_problem_solution {r : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (φ : (Fin r → ℝ) → ℝ) (hφ : ConvexOn ℝ (Set.Icc α β) φ) :
    IsProbabilityMeasure (genEMMeasure P α β) ∧
    genEMMeasure P α β (Set.Icc α β)ᶜ = 0 ∧
    (∀ Λ : Finset (Fin r), ∫ ξ, ∏ k ∈ Λ, ξ k ∂(genEMMeasure P α β) = ∫ ξ, ∏ k ∈ Λ, ξ k ∂P) ∧
    ∫ ξ, φ ξ ∂(genEMMeasure P α β) = genEMBound P α β φ ∧
    ∀ P' : Measure (Fin r → ℝ), IsProbabilityMeasure P' → P' (Set.Icc α β)ᶜ = 0 →
      (∀ Λ : Finset (Fin r), ∫ ξ, ∏ k ∈ Λ, ξ k ∂P' = ∫ ξ, ∏ k ∈ Λ, ξ k ∂P) →
      ∫ ξ, φ ξ ∂P' ≤ ∫ ξ, φ ξ ∂(genEMMeasure P α β) := by sorry

end KallMayerSLP.RecourseBounds
