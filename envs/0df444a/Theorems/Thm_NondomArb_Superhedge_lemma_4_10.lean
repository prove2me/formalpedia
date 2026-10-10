-- Prove2me | Theorems.Thm_NondomArb_Superhedge_lemma_4_10
-- name    : NondomArb.Superhedge.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:17.051141+00:00
-- url     : https://prove2.me/theorems/a4191ff0-29f6-435a-804f-1499da086c65
-- title:
--   Lemma 4.10 — ℰ_t(f) = sup_{Q∈𝒬_t(ω)} E_Q[f(ω,·)] is upper semianalytic and has a measurable one-step superhedge (4.10)
-- statement:
--   Consider the multi-period market of §1.2 without options ($e=0$). For $t<T$ and $\omega\in\Omega_t$ let
--   $$\mathcal Q_t(\omega)=\{Q\in\mathfrak P(\Omega_1):\ Q\lll\mathcal P_t(\omega),\ E_Q[\Delta S_{t+1}(\omega,\cdot)]=0\}.$$
--
--   **Lemma.** Let NA($\mathcal P$) hold, let $t\in\{0,\dots,T-1\}$ and let $f:\Omega_t\times\Omega_1\to\overline{\mathbb R}$ be upper semianalytic. Then
--   $$\mathcal E_t(f):\Omega_t\to\overline{\mathbb R},\qquad \mathcal E_t(f)(\omega):=\sup_{Q\in\mathcal Q_t(\omega)}E_Q[f(\omega,\cdot)]$$
--   is upper semianalytic. Moreover, there exists a universally measurable function $y(\cdot):\Omega_t\to\mathbb R^d$ such that
--   $$\mathcal E_t(f)(\omega)+y(\omega)\Delta S_{t+1}(\omega,\cdot)\ge f(\omega,\cdot)\qquad\mathcal P_t(\omega)\text{-q.s.}\tag{4.10}$$
--   for all $\omega\in\Omega_t$ such that $\mathrm{NA}(\mathcal P_t(\omega))$ holds and $f(\omega,\cdot)>-\infty$ $\mathcal P_t(\omega)$-q.s.
--
--   This is a measurable version of the one-period superhedging theorem; applied recursively it produces the dynamic superhedging price and the optimal strategy.
--
--   **Formalization Note** $E_Q$ is the extended expectation (1.1) in `EReal`, and the left side of (4.10) is `EReal` addition of a real number to $\mathcal E_t(f)(\omega)$. "$\mathcal P_t(\omega)$-q.s." means $P$-a.s. for every $P\in\mathcal P_t(\omega)$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 25, Lemma 4.10, (4.10); p. 22, Lemma 4.8 (definition of 𝒬_t)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_Model
open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.Superhedge

/-- **Lemma 4.10** (p. 25). (No options, `e = 0`.) Under NA(𝒫), for an upper semianalytic
`f : Ω_t × Ω₁ → [−∞, ∞]`, the one-step value `ℰ_t(f)(ω) = sup_{Q ∈ 𝒬_t(ω)} E_Q[f(ω, ·)]` is upper
semianalytic, and a universally measurable `y : Ω_t → ℝ^d` satisfies (4.10)
`ℰ_t(f)(ω) + y(ω) ΔS_{t+1}(ω, ·) ≥ f(ω, ·)` `𝒫_t(ω)`-q.s. wherever NA(𝒫_t(ω)) holds and
`f(ω, ·) > −∞` `𝒫_t(ω)`-q.s. -/
theorem lemma_4_10 {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁]
    [MeasurableSpace Ω₁] [BorelSpace Ω₁] {T d : ℕ}
    (M : Market Ω₁ T d 0) (hM : M.Standing) (hNA : M.NA) (t : ℕ) (ht : t < T)
    (f : (Fin t → Ω₁) × Ω₁ → EReal) (hf : IsUpperSemianalytic f) :
    IsUpperSemianalytic (M.condSup t f) ∧
      ∃ y : (Fin t → Ω₁) → (Fin d → ℝ), IsUMeasurable y ∧
        ∀ ω : Fin t → Ω₁, M.LocalNA t ω →
          (∀ P ∈ M.Pt t ω, ∀ᵐ x ∂(P : Measure Ω₁), ⊥ < f (ω, x)) →
          ∀ P ∈ M.Pt t ω, ∀ᵐ x ∂(P : Measure Ω₁),
            f (ω, x) ≤ M.condSup t f ω + ((y ω ⬝ᵥ M.incr t ω x : ℝ) : EReal) := by sorry

end NondomArb.Superhedge
