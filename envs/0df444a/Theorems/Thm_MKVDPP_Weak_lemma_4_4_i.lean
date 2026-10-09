-- Prove2me | Theorems.Thm_MKVDPP_Weak_lemma_4_4_i
-- name    : MKVDPP.Weak.lemma_4_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:29:29.11255+00:00
-- url     : https://prove2.me/theorems/ccc8584b-05a2-43dd-a638-0a7d07efbddd
-- title:
--   Lemma 4.4(i), p. 17 — weak controls induce weak control rules ℙ̄^γ ∈ 𝒫̄_W(t,ν), and conversely
-- statement:
--   Under the standing assumptions, let $t\in[0,T]$ and $\nu\in\mathcal P(\mathcal C^n)$.
--
--   1. For every weak control $\gamma\in\Gamma_W(t,\nu)$,
--   $$\bar{\mathbb P}^\gamma:=\mathbb P^\gamma\circ\big(X^\gamma,A^\gamma,W^\gamma,B^\gamma,\hat\mu^\gamma\big)^{-1}\in\bar{\mathcal P}_W(t,\nu).$$
--   2. Conversely, let $\bar{\mathbb P}\in\bar{\mathcal P}_W(t,\nu)$ be such that, $\bar{\mathbb P}$-a.s., $A_s=\int_t^{s\vee t}\pi(\bar\alpha_r)\,dr$ for all $s\in[0,T]$. Then there is $\gamma\in\Gamma_W(t,\nu)$ with $\mathbb P^\gamma\circ(X^\gamma,A^\gamma,W^\gamma,B^\gamma,\hat\mu^\gamma)^{-1}=\bar{\mathbb P}$.
--
--   The lemma identifies the weak formulation with a set of probability measures on a fixed Polish space, which is what makes measurable selection available.
--
--   **Formalization Note** The hypothesis on $A$ in part 2 is not on the page. It is necessary: $A^\gamma$ is by definition (2.6) the integral of $\pi(\alpha^\gamma)$ from $t$, so every image $\bar{\mathbb P}^\gamma$ satisfies it, while Definition 4.1 does not constrain $A$ before $t$ (only through $\hat\nu(t)$, which may be arbitrary in its $A$-marginal) nor force $A$ to be absolutely continuous after $t$. The paper's proof builds $\gamma$ on $\bar\Omega$ with $A^\gamma$ given by (2.6), which equals the canonical $A$ exactly under this hypothesis. In the hypothesis, $\partial$ is read as $u_0$, which affects only a null set of times.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 17, Lemma 4.4(i), (4.7)

import Mathlib
import Definitions.Def_MKVDPP_Weak_Setting
import Definitions.Def_MKVDPP_Weak_WeakControl
import Definitions.Def_MKVDPP_Weak_Canonical

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MKVDPP.Weak

/-- **Lemma 4.4 (i)** (p. 17). Every weak control `γ ∈ Γ_W(t,ν)` induces the weak control rule
`ℙ̄^γ := ℙ^γ ∘ (X^γ, A^γ, W^γ, B^γ, μ̂^γ)⁻¹ ∈ 𝒫̄_W(t,ν)` (4.7); conversely every
`ℙ̄ ∈ 𝒫̄_W(t,ν)` whose canonical `A` is `ℙ̄`-a.s. the path `s ↦ ∫_t^{s∨t} π(ᾱ_r) dr` of
Remark 2.4 is of this form for some `γ ∈ Γ_W(t,ν)` (the page omits this hypothesis; without it the
converse fails, since `A^γ` is always of that form). -/
theorem lemma_4_4_i
    {T : ℝ≥0} (hT : 0 < T) {n d ℓ : ℕ} {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U] [MeasurableSpace U] [BorelSpace U]
    (u₀ : U) (p : ℝ) (hp : 0 ≤ p) (π : U → ℝ) (hπ : IsControlEncoding π)
    (c : Coeffs T n d ℓ U) (hc : c.IsAdmissible)
    (t : ℝ≥0) (ht : t ≤ T) (ν : ProbabilityMeasure (Cpath T n)) :
    (∀ (Ω : Type) [MeasurableSpace Ω] (γ : WeakControl c u₀ p π Ω t ν),
      ∃ Pbar ∈ PbarW hπ c u₀ p t ν,
        (Pbar : Measure (OmegaBar T n d ℓ)) = γ.P.map (embedBar γ)) ∧
    ∀ Pbar ∈ PbarW hπ c u₀ p t ν,
      (∀ᵐ ω ∂(Pbar : Measure (OmegaBar T n d ℓ)), ∀ s : ℝ≥0, s ≤ T →
        pathAt (Ac ω) s = ∫ r in Set.Ioc (t:ℝ) (max s t), π (alphaBarU π u₀ r.toNNReal ω)) →
      ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (γ : @WeakControl T n d ℓ U _ _ c u₀ p π Ω mΩ t ν),
        γ.P.map (@embedBar T n d ℓ U _ _ c u₀ p π Ω mΩ t ν γ) = (Pbar : Measure (OmegaBar T n d ℓ)) := by sorry

end MKVDPP.Weak
