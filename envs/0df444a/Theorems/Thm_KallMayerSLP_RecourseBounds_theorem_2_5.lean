-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_theorem_2_5
-- name    : KallMayerSLP.RecourseBounds.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:02.703389+00:00
-- url     : https://prove2.me/theorems/3988a4d6-e655-487f-95a4-ec22e3fecf51
-- title:
--   Theorem 2.5 — E–M upper bound on the expected recourse, independent components
-- statement:
--   Consider the two-stage problem with fixed recourse matrix $W$, deterministic $q$ and random data $T(\xi)=T+\sum_jT^j\xi_j$, $h(\xi)=h+\sum_jh^j\xi_j$, under
--
--   1. Assumption 2.1 (complete fixed recourse): $\{Wy\mid y\ge0\}=\mathbb R^{m_2}$;
--   2. Assumption 2.2: $\{u\mid W^{\mathsf T}u\le q\}\ne\emptyset$.
--
--   Let the components of $\xi$ be stochastically independent, $\operatorname{supp}\mathbb P_\xi\subset\Xi=\times_{i=1}^r[\alpha_i,\beta_i]$ with $\alpha_i<\beta_i$, and $\mu=\mathbb E_\xi[\xi]$. Let $\eta$ have the product E–M distribution $\mathbb P_\eta=\mathbb P_{\eta_1}\times\dots\times\mathbb P_{\eta_r}$ of the two-point laws (2.19). Then for every first-stage decision $x$ the expected recourse is bounded above:
--   $$
--   \mathcal Q(x)=\mathbb E_\xi[Q(x;T(\xi),h(\xi))]\le\mathbb E_\eta[Q(x;T(\eta),h(\eta))].
--   $$
--
--   The right side is a finite sum over the $2^r$ vertices of $\Xi$, so it is computable from the means alone.
--
--   **Formalization Note** $\mathbb E_\eta[\cdot]$ is the platform's `emUpperBound α β μ`; independence is `iIndepFun` of the coordinate maps.
--
--   Differences from the source:
--   - encoding: random vector ξ with distribution IP_ξ, supp IP_ξ ⊂ Ξ = ×ᵢ[αᵢ, βᵢ] → probability measure P on Fin r → ℝ with P(Ξᶜ) = 0, Ξ = Set.Icc α β; reason: every quantity depends only on the law of ξ; Ξ is closed, so supp IP_ξ ⊂ Ξ is P(Ξᶜ) = 0; ℝ^r is Fin r → ℝ (0-based index)
--   - encoding: components of ξ stochastically independent → iIndepFun of the coordinate maps under P; reason: the definition of independence of the components
--   - encoding: Q(x; T(ξ), h(ξ)) = min{qᵀy | Wy = h(ξ) − T(ξ)x, y ≥ 0} → (NumStochOpt.Bounds.recourseCost W q h(ξ) T(ξ) x).toReal, the EReal infimum read as a real; reason: under Assumptions 2.1 and 2.2 (both hypotheses) the LP is feasible and bounded, so the infimum is finite and is the attained minimum
--   - encoding: Assumption 2.2: {u | Wᵀu ≤ q(ξ)} ≠ ∅ for all ξ ∈ Ξ, with q(ξ) ≡ q deterministic (p.210) → NumStochOpt.Bounds.DualFeasible W q (∃ u, Wᵀ u ≤ q); reason: with q deterministic the condition does not depend on ξ
--   - encoding: IE_η[·] with IP_η from (2.19)–(2.20) → NumStochOpt.Bounds.emUpperBound α β μ; reason: the expectation of a product of two-point laws is the weighted vertex sum
--   - encoding: the two-point laws (2.19) divide by βᵢ − αᵢ → hypothesis αᵢ < βᵢ for every i; reason: excludes exactly the boxes where (2.19) is undefined
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Theorem 2.5, (2.25), p.214 (PDF 223)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky
import Definitions.Def_KallMayerSLP_RecourseBounds_recourseValue

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, Theorem 2.5 — the E–M upper bound on the expected recourse (independent case).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Theorem 2.5, (2.25), printed p.214
(PDF 223): "Assume that the components of `ξ` are stochastically independent and that
`supp IP_ξ ⊂ Ξ = ×_{i=1}^r [αᵢ, βᵢ]` with `μ = IE_ξ[ξ] ∈ Ξ`. Given the Assumptions 2.1 and 2.2, with
the E–M distribution defined by (2.19) and (2.20) the expected recourse
`Q(x) = IE_ξ[Q(x; T(ξ), h(ξ))]` is bounded above according to `Q(x) ≤ IE_η[Q(x; T(η), h(η))]`."

Standing assumptions of the section: fixed recourse matrix `W`, deterministic `q` (p.210, "Finally,
assume that `q(ξ) ≡ q`"), `T(ξ)`, `h(ξ)` affine in `ξ` (2.1); Assumption 2.1 (p.203): complete fixed
recourse `{Wy | y ≥ 0} = ℝ^{m₂}` (2.6), the platform's `NumStochOpt.Bounds.CompleteRecourse W`;
Assumption 2.2 (p.203), with `q` deterministic: `{u | Wᵀu ≤ q} ≠ ∅` (2.8), the platform's
`NumStochOpt.Bounds.DualFeasible W q`.

**Formalization Note.** `IP_ξ` is a probability measure `P` on `Fin r → ℝ`, independence is
`iIndepFun` of the coordinate maps under `P`, `supp IP_ξ ⊂ Ξ` is `P(Ξᶜ) = 0`. `IE_η[·]` for the product
of the two-point laws (2.19)–(2.20) is the platform's `NumStochOpt.Bounds.emUpperBound α β μ`
(sum over the `2^r` vertices with weights `∏ᵢ` of (2.19)). `αᵢ < βᵢ` is the nondegeneracy (2.19)
divides by; `μ ∈ Ξ` follows from `P(Ξᶜ) = 0`. The first-stage decision `x ∈ ℝ^{n₁}` is arbitrary. -/
theorem theorem_2_5 {r m₂ n₂ n₁ : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hαβ : ∀ i, α i < β i) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (hind : ProbabilityTheory.iIndepFun (fun i (ξ : Fin r → ℝ) => ξ i) P)
    (W : Matrix (Fin m₂) (Fin n₂) ℝ) (q : Fin n₂ → ℝ)
    (hW : NumStochOpt.Bounds.CompleteRecourse W) (hq : NumStochOpt.Bounds.DualFeasible W q)
    (T₀ : Matrix (Fin m₂) (Fin n₁) ℝ) (T : Fin r → Matrix (Fin m₂) (Fin n₁) ℝ)
    (h₀ : Fin m₂ → ℝ) (h : Fin r → Fin m₂ → ℝ) (x : Fin n₁ → ℝ) :
    ∫ ξ, recourseValue W q T₀ T h₀ h x ξ ∂P ≤
      NumStochOpt.Bounds.emUpperBound α β (fun i => ∫ ξ, ξ i ∂P)
        (recourseValue W q T₀ T h₀ h x) := by sorry

end KallMayerSLP.RecourseBounds
