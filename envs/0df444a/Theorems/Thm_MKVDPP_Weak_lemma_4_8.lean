-- Prove2me | Theorems.Thm_MKVDPP_Weak_lemma_4_8
-- name    : MKVDPP.Weak.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:28:58.812254+00:00
-- url     : https://prove2.me/theorems/cbc21d84-6efc-4ff1-8733-6822ad8d1657
-- title:
--   Lemma 4.8, p. 19 — r.c.p.d. of a weak control rule at a 𝔾̄^t-stopping time are again weak control rules
-- statement:
--   Under the standing assumptions, let $(t,\hat\nu)\in[0,T]\times\mathcal P(\hat\Omega)$, $\bar{\mathbb P}\in\hat{\mathcal P}_W(t,\hat\nu)$, let $\bar\tau$ be a $\bar{\mathbb G}^t$-stopping time with values in $[t,T]$, and let $(\bar{\mathbb P}^{\bar{\mathcal G}^t_{\bar\tau}}_{\bar\omega})_{\bar\omega\in\bar\Omega}$ be a family of r.c.p.d. of $\bar{\mathbb P}$ knowing $\bar{\mathcal G}^t_{\bar\tau}$. Then
--   $$\bar{\mathbb P}^{\bar{\mathcal G}^t_{\bar\tau}}_{\bar\omega}\in\hat{\mathcal P}_W\big(\bar\tau(\bar\omega),\hat\mu_{\bar\tau(\bar\omega)}(\bar\omega)\big)\qquad\text{for }\bar{\mathbb P}\text{-a.e. }\bar\omega\in\bar\Omega.$$
--
--   This stability under conditioning gives the inequality $V_W(t,\nu)\le$ (right-hand side of (3.2)).
--
--   **Formalization Note** The r.c.p.d. includes the atom condition $\bar{\mathbb P}_{\bar\omega}[[\bar\omega]_{\mathcal G}]=1$ for every $\bar\omega$ (Notations (iii)). $\bar{\mathcal G}^t_{\bar\tau}$ is Mathlib's $\sigma$-algebra of a stopping time.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 19, Lemma 4.8

import Mathlib
import Definitions.Def_MKVDPP_Weak_Setting
import Definitions.Def_MKVDPP_Weak_WeakControl
import Definitions.Def_MKVDPP_Weak_Canonical

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MKVDPP.Weak

/-- **Lemma 4.8** (p. 19). For `ℙ̄ ∈ 𝒫̂_W(t, ν̂)`, a `𝔾̄^t`-stopping time `τ̄` with values in
`[t,T]` and an r.c.p.d. `(ℙ̄_ω̄)` of `ℙ̄` knowing `𝒢̄^t_τ̄`, one has
`ℙ̄_ω̄ ∈ 𝒫̂_W(τ̄(ω̄), μ̂_{τ̄(ω̄)}(ω̄))` for `ℙ̄`-a.e. `ω̄`. -/
theorem lemma_4_8
    {T : ℝ≥0} (hT : 0 < T) {n d ℓ : ℕ} {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U] [MeasurableSpace U] [BorelSpace U]
    (u₀ : U) (p : ℝ) (hp : 0 ≤ p) (π : U → ℝ) (hπ : IsControlEncoding π)
    (c : Coeffs T n d ℓ U) (hc : c.IsAdmissible)
    (t : ℝ≥0) (ht : t ≤ T) (νh : ProbabilityMeasure (OmegaHat T n d ℓ))
    (P : ProbabilityMeasure (OmegaBar T n d ℓ)) (hP : P ∈ PhatW hπ c u₀ p t νh)
    (τ : OmegaBar T n d ℓ → ℝ≥0)
    (hτ : IsStoppingTime (Gbar T n d ℓ t) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, t ≤ τ ω ∧ τ ω ≤ T)
    (κ : OmegaBar T n d ℓ → ProbabilityMeasure (OmegaBar T n d ℓ))
    (hκ : IsRCPD hτ.measurableSpace (P : Measure (OmegaBar T n d ℓ)) κ) :
    ∀ᵐ ω ∂(P : Measure (OmegaBar T n d ℓ)),
      κ ω ∈ PhatW hπ c u₀ p (τ ω) (pathAt (muHatOf ω) (τ ω)) := by sorry

end MKVDPP.Weak
