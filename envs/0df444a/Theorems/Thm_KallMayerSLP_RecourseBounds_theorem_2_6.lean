-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_theorem_2_6
-- name    : KallMayerSLP.RecourseBounds.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:15:29.809393+00:00
-- url     : https://prove2.me/theorems/50bdb5cc-b5c3-4ddc-b026-8487383dede2
-- title:
--   Theorem 2.6 — generalized E–M upper bound on the expected recourse
-- statement:
--   Consider the two-stage problem with fixed recourse matrix $W$, deterministic $q$ and random data $T(\xi)=T+\sum_jT^j\xi_j$, $h(\xi)=h+\sum_jh^j\xi_j$, under
--
--   1. Assumption 2.1 (complete fixed recourse): $\{Wy\mid y\ge0\}=\mathbb R^{m_2}$;
--   2. Assumption 2.2: $\{u\mid W^{\mathsf T}u\le q\}\ne\emptyset$.
--
--   Let $\operatorname{supp}\mathbb P_\xi\subset\Xi=\times_{i=1}^r[\alpha_i,\beta_i]$, with the components of $\xi$ possibly dependent, and let $\mathbb Q$ be the generalized E–M distribution (2.30). Then for every first-stage decision $x$,
--   $$
--   \mathcal Q(x)=\mathbb E_\xi[Q(x;T(\xi),h(\xi))]\le\int_\Xi Q(x;T(\eta),h(\eta))\,\mathbb Q(d\eta)=\sum_{\nu=1}^{2^r}Q(x;T(v^\nu),h(v^\nu))\,\mathbb Q(v^\nu).
--   $$
--
--   This extends Theorem 2.5 to dependent components; the bound needs the $2^r$ joint moments of $\xi$ rather than only its means.
--
--   **Formalization Note** The right side is `genEMBound P α β` applied to the recourse function.
--
--   Differences from the source:
--   - encoding: random vector ξ with distribution IP_ξ, supp IP_ξ ⊂ Ξ = ×ᵢ[αᵢ, βᵢ] → probability measure P on Fin r → ℝ with P(Ξᶜ) = 0, Ξ = Set.Icc α β; reason: every quantity depends only on the law of ξ; Ξ is closed, so supp IP_ξ ⊂ Ξ is P(Ξᶜ) = 0; ℝ^r is Fin r → ℝ (0-based index)
--   - encoding: Q(x; T(ξ), h(ξ)) = min{qᵀy | Wy = h(ξ) − T(ξ)x, y ≥ 0} → (NumStochOpt.Bounds.recourseCost W q h(ξ) T(ξ) x).toReal, the EReal infimum read as a real; reason: under Assumptions 2.1 and 2.2 (both hypotheses) the LP is feasible and bounded, so the infimum is finite and is the attained minimum
--   - encoding: Assumption 2.2: {u | Wᵀu ≤ q(ξ)} ≠ ∅ for all ξ ∈ Ξ, with q(ξ) ≡ q deterministic (p.210) → NumStochOpt.Bounds.DualFeasible W q (∃ u, Wᵀ u ≤ q); reason: with q deterministic the condition does not depend on ξ
--   - generalization: (2.26)/(2.30) divide by βᵢ − αᵢ, so the book's boxes have αᵢ < βᵢ → αᵢ = βᵢ allowed: a degenerate coordinate gets the point mass at its single value (vertexProb); reason: for αᵢ < βᵢ vertexProb is exactly the book's product of two-point laws, so the statement specializes to the book's
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Theorem 2.6, (2.32), p.217 (PDF 226)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMBound
import Definitions.Def_KallMayerSLP_RecourseBounds_recourseValue

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, Theorem 2.6 — the generalized E–M upper bound on the expected recourse.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Theorem 2.6, (2.32), printed p.217
(PDF 226): "Assume that `supp IP_ξ ⊂ Ξ = ×_{i=1}^r [αᵢ, βᵢ]` such that also `μ = IE_ξ[ξ] ∈ Ξ`. Under
the Assumptions 2.1 and 2.2 and with the generalized E–M distribution `Q` as defined in (2.30),
according to (2.31) the expected recourse `Q(x) = IE_ξ[Q(x; T(ξ), h(ξ))]` is bounded above as
`Q(x) ≤ ∫_Ξ Q(x; T(η), h(η)) Q(dη) = Σ_{ν=1}^{2^r} Q(x; T(v^ν), h(v^ν)) Q(v^ν)`."

Standing assumptions of the section: fixed recourse matrix `W`, deterministic `q` (p.210), `T(ξ)`,
`h(ξ)` affine in `ξ` (2.1); Assumption 2.1 (p.203): `{Wy | y ≥ 0} = ℝ^{m₂}` (2.6), `NumStochOpt.Bounds.CompleteRecourse W`;
Assumption 2.2 (p.203), with `q` deterministic: `{u | Wᵀu ≤ q} ≠ ∅` (2.8),
`NumStochOpt.Bounds.DualFeasible W q`.

**Formalization Note.** `IP_ξ` is a probability measure `P` on `Fin r → ℝ` with `P(Ξᶜ) = 0`; the
components of `ξ` may be dependent. The right side is the vertex sum `genEMBound P α β`, i.e.
`Σ_v Q(v) · Q(x; T(v), h(v))`. `μ ∈ Ξ` follows from `P(Ξᶜ) = 0`. The first-stage decision `x` is
arbitrary. -/
theorem theorem_2_6 {r m₂ n₂ n₁ : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (W : Matrix (Fin m₂) (Fin n₂) ℝ) (q : Fin n₂ → ℝ)
    (hW : NumStochOpt.Bounds.CompleteRecourse W) (hq : NumStochOpt.Bounds.DualFeasible W q)
    (T₀ : Matrix (Fin m₂) (Fin n₁) ℝ) (T : Fin r → Matrix (Fin m₂) (Fin n₁) ℝ)
    (h₀ : Fin m₂ → ℝ) (h : Fin r → Fin m₂ → ℝ) (x : Fin n₁ → ℝ) :
    ∫ ξ, recourseValue W q T₀ T h₀ h x ξ ∂P ≤
      genEMBound P α β (recourseValue W q T₀ T h₀ h x) := by sorry

end KallMayerSLP.RecourseBounds
