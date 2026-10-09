-- Prove2me | Theorems.Thm_MKVDPP_Weak_lemma_4_10
-- name    : MKVDPP.Weak.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:29:05.306224+00:00
-- url     : https://prove2.me/theorems/e683e3c7-0e80-48eb-b058-715ffd146d0b
-- title:
--   Lemma 4.10, p. 20 — universally measurable ε-optimal rules Q̄^ε and their concatenation ℙ̄^{M,ε} ∈ 𝒫̄_W(t,ν) after τ̄
-- statement:
--   Under the standing assumptions, let $(t,\nu)\in[0,T]\times\mathcal P(\mathcal C^n)$, $\bar{\mathbb P}\in\bar{\mathcal P}_W(t,\nu)$, let $\bar\tau$ be a $\bar{\mathbb G}^t$-stopping time with values in $[t,T]$, and let $\varepsilon>0$. Then there is a family $(\bar{\mathbb Q}^\varepsilon_{s,\hat\nu,M})$ indexed by $(s,\hat\nu,M)\in[0,T]\times\mathcal P(\hat\Omega)\times\mathbb R_+$ such that:
--
--   1. $(s,\hat\nu,M)\mapsto\bar{\mathbb Q}^\varepsilon_{s,\hat\nu,M}$ is universally measurable, and whenever $\hat{\mathcal P}^M_W(s,\hat\nu)\neq\emptyset$, writing $\nu':=\hat\nu\circ\hat X^{-1}$,
--   $$\bar{\mathbb Q}^\varepsilon_{s,\hat\nu,M}\in\hat{\mathcal P}^M_W(s,\hat\nu),\qquad J(s,\bar{\mathbb Q}^\varepsilon_{s,\hat\nu,M})\ge\begin{cases}V^M_W(s,\nu')-\varepsilon,&V^M_W(s,\nu')<\infty,\\ 1/\varepsilon,&V^M_W(s,\nu')=\infty;\end{cases}$$
--   2. there is a $\bar{\mathbb P}$-integrable, $\bar{\mathcal G}^t_{\bar\tau}$-measurable $\hat M:\bar\Omega\to\mathbb R_+$ such that for every constant $M\ge0$ there is $\bar{\mathbb P}^{M,\varepsilon}\in\bar{\mathcal P}_W(t,\nu)$ with $\bar{\mathbb P}^{M,\varepsilon}=\bar{\mathbb P}$ on $\bar{\mathcal F}_{\bar\tau}$, for which $\big(\bar{\mathbb Q}^\varepsilon_{\bar\tau(\bar\omega),\hat\mu_{\bar\tau(\bar\omega)}(\bar\omega),M+\hat M(\bar\omega)}\big)_{\bar\omega\in\bar\Omega}$ is a version of the r.c.p.d. of $\bar{\mathbb P}^{M,\varepsilon}$ knowing $\bar{\mathcal G}^t_{\bar\tau}$.
--
--   This concatenation result gives the inequality $V_W(t,\nu)\ge$ (right-hand side of (3.2)).
--
--   **Formalization Note** The page uses the letter $t$ both for the fixed initial time and for the index of $\bar{\mathbb Q}^\varepsilon$; the index is written $s$ here. The lemma is stated with the hypothesis that $\bar\tau$ is also an $\bar{\mathbb F}$-stopping time, which holds because $\bar{\mathcal G}^t_s\subseteq\bar{\mathcal F}_s$ and is needed to name $\bar{\mathcal F}_{\bar\tau}$. Universal measurability is that of `BertsekasShreve.AnalyticSelection.IsUniversallyMeasurableFun` on the whole index space.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 20, Lemma 4.10, (4.11)

import Mathlib
import Definitions.Def_MKVDPP_Weak_Setting
import Definitions.Def_MKVDPP_Weak_WeakControl
import Definitions.Def_MKVDPP_Weak_Canonical
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MKVDPP.Weak

/-- **Lemma 4.10** (p. 20). A universally measurable family `Q̄^ε_{s,ν̂,M}` of `ε`-optimal weak
control rules (4.11), and, for `ℙ̄ ∈ 𝒫̄_W(t,ν)` and a `𝔾̄^t`-stopping time `τ̄` in `[t,T]`, an
integrable `𝒢̄^t_τ̄`-measurable `M̂ ≥ 0` such that for every `M ≥ 0` some `ℙ̄^{M,ε} ∈ 𝒫̄_W(t,ν)`
agrees with `ℙ̄` on `ℱ̄_τ̄` and has `(Q̄^ε_{τ̄(ω̄), μ̂_{τ̄(ω̄)}(ω̄), M + M̂(ω̄)})` as an r.c.p.d. knowing
`𝒢̄^t_τ̄`. -/
theorem lemma_4_10
    {T : ℝ≥0} (hT : 0 < T) {n d ℓ : ℕ} {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U] [MeasurableSpace U] [BorelSpace U]
    (u₀ : U) (p : ℝ) (hp : 0 ≤ p) (π : U → ℝ) (hπ : IsControlEncoding π)
    (c : Coeffs T n d ℓ U) (hc : c.IsAdmissible)
    (t : ℝ≥0) (ht : t ≤ T) (ν : ProbabilityMeasure (Cpath T n))
    (P : ProbabilityMeasure (OmegaBar T n d ℓ)) (hP : P ∈ PbarW hπ c u₀ p t ν)
    (τ : OmegaBar T n d ℓ → ℝ≥0)
    (hτG : IsStoppingTime (Gbar T n d ℓ t) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτF : IsStoppingTime (Fbar T n d ℓ) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, t ≤ τ ω ∧ τ ω ≤ T) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : Set.Icc (0:ℝ≥0) T × ProbabilityMeasure (OmegaHat T n d ℓ) × ℝ≥0 →
        ProbabilityMeasure (OmegaBar T n d ℓ),
      BertsekasShreve.AnalyticSelection.IsUniversallyMeasurableFun Set.univ
        (fun x : (Set.univ : Set (Set.Icc (0:ℝ≥0) T × ProbabilityMeasure (OmegaHat T n d ℓ) × ℝ≥0))
          => Q x.1) ∧
      (∀ (s : Set.Icc (0:ℝ≥0) T) (νh : ProbabilityMeasure (OmegaHat T n d ℓ)) (M : ℝ≥0),
        (PhatWM hπ c u₀ p s νh M).Nonempty →
          Q (s, νh, M) ∈ PhatWM hπ c u₀ p s νh M ∧
          (VWM hπ c u₀ p s (margXhat νh) M < ⊤ →
            VWM hπ c u₀ p s (margXhat νh) M - (ε : EReal) ≤ Jbar hπ c u₀ s (Q (s, νh, M))) ∧
          (VWM hπ c u₀ p s (margXhat νh) M = ⊤ →
            ((1 / ε : ℝ) : EReal) ≤ Jbar hπ c u₀ s (Q (s, νh, M)))) ∧
      ∃ Mhat : OmegaBar T n d ℓ → ℝ≥0,
        Integrable (fun ω => (Mhat ω : ℝ)) (P : Measure (OmegaBar T n d ℓ)) ∧
        Measurable[hτG.measurableSpace] Mhat ∧
        ∀ M : ℝ≥0, ∃ P' ∈ PbarW hπ c u₀ p t ν,
          (∀ A : Set (OmegaBar T n d ℓ), MeasurableSet[hτF.measurableSpace] A →
            (P' : Measure (OmegaBar T n d ℓ)) A = (P : Measure (OmegaBar T n d ℓ)) A) ∧
          IsRCPD hτG.measurableSpace (P' : Measure (OmegaBar T n d ℓ))
            (fun ω => Q (⟨τ ω, ⟨bot_le, (hτT ω).2⟩⟩, pathAt (muHatOf ω) (τ ω), M + Mhat ω)) := by sorry

end MKVDPP.Weak
