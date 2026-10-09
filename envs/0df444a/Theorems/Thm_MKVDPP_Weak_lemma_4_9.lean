-- Prove2me | Theorems.Thm_MKVDPP_Weak_lemma_4_9
-- name    : MKVDPP.Weak.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:29:03.387461+00:00
-- url     : https://prove2.me/theorems/0b82ea48-ff78-423d-ba25-36c84892fe20
-- title:
--   Lemma 4.9, p. 20 — 𝒫̂_W(t,ν̂) depends on ν̂ only through ν̂(t), and V_W, V^M_W are suprema over 𝒫̂_W(t,ν̂₁)
-- statement:
--   Under the standing assumptions, let $t\in[0,T]$, $\hat\nu_1,\hat\nu_2\in\mathcal P(\hat\Omega)$ and $\nu\in\mathcal P(\mathcal C^n)$ with $\hat\nu_1\circ X_{t\wedge\cdot}^{-1}=\hat\nu_2\circ X_{t\wedge\cdot}^{-1}=\nu(t)$. Write $A^t_\cdot:=A_{\cdot\vee t}-A_t$ and similarly $W^t,B^t$.
--
--   1. For every $\bar{\mathbb P}_1\in\hat{\mathcal P}_W(t,\hat\nu_1)$ there is $\bar{\mathbb P}_2\in\hat{\mathcal P}_W(t,\hat\nu_2)$ with
--   $$\bar{\mathbb P}_1\circ(X,A^t,W^t,B^t)^{-1}=\bar{\mathbb P}_2\circ(X,A^t,W^t,B^t)^{-1},$$
--   so that $J(t,\bar{\mathbb P}_1)=J(t,\bar{\mathbb P}_2)$.
--   2. Consequently
--   $$V_W(t,\nu)=\sup_{\bar{\mathbb P}\in\hat{\mathcal P}_W(t,\hat\nu_1)}J(t,\bar{\mathbb P}),\qquad V^M_W(t,\nu)=\sup_{\bar{\mathbb P}\in\hat{\mathcal P}^M_W(t,\hat\nu_1)}J(t,\bar{\mathbb P})\quad(M\ge0).$$
--
--   The lemma lets the selection in Lemma 4.10 be indexed by $\hat\nu$ while the value depends only on $\nu$.
--
--   **Formalization Note** The equality of $J$ is stated as a separate conclusion; the paper's "so that" presents it as a consequence. $M$ ranges over $[0,\infty)$. The paper omits the proof ("almost the same as that of Lemma 3.10").
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 20, Lemma 4.9

import Mathlib
import Definitions.Def_MKVDPP_Weak_Setting
import Definitions.Def_MKVDPP_Weak_WeakControl
import Definitions.Def_MKVDPP_Weak_Canonical

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MKVDPP.Weak

/-- **Lemma 4.9** (p. 20). If `ν̂₁ ∘ X̂_{t∧·}⁻¹ = ν̂₂ ∘ X̂_{t∧·}⁻¹ = ν(t)`, every
`ℙ̄₁ ∈ 𝒫̂_W(t, ν̂₁)` has a companion `ℙ̄₂ ∈ 𝒫̂_W(t, ν̂₂)` with the same law of `(X, A^t, W^t, B^t)`
and the same reward; consequently `V_W(t,ν)` and `V^M_W(t,ν)` are suprema over `𝒫̂_W(t, ν̂₁)` and
`𝒫̂^M_W(t, ν̂₁)`. -/
theorem lemma_4_9
    {T : ℝ≥0} (hT : 0 < T) {n d ℓ : ℕ} {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U] [MeasurableSpace U] [BorelSpace U]
    (u₀ : U) (p : ℝ) (hp : 0 ≤ p) (π : U → ℝ) (hπ : IsControlEncoding π)
    (c : Coeffs T n d ℓ U) (hc : c.IsAdmissible)
    (t : ℝ≥0) (ht : t ≤ T) (νh₁ νh₂ : ProbabilityMeasure (OmegaHat T n d ℓ))
    (ν : ProbabilityMeasure (Cpath T n))
    (h₁ : margX t νh₁ = lawStop ν t) (h₂ : margX t νh₂ = lawStop ν t) :
    (∀ P₁ ∈ PhatW hπ c u₀ p t νh₁, ∃ P₂ ∈ PhatW hπ c u₀ p t νh₂,
      (P₁ : Measure (OmegaBar T n d ℓ)).map (shiftBar t) =
        (P₂ : Measure (OmegaBar T n d ℓ)).map (shiftBar t) ∧
      Jbar hπ c u₀ t P₁ = Jbar hπ c u₀ t P₂) ∧
    VW c u₀ p π t ν = ⨆ P ∈ PhatW hπ c u₀ p t νh₁, Jbar hπ c u₀ t P ∧
    ∀ M : ℝ≥0, VWM hπ c u₀ p t ν M = ⨆ P ∈ PhatWM hπ c u₀ p t νh₁ M, Jbar hπ c u₀ t P := by sorry

end MKVDPP.Weak
