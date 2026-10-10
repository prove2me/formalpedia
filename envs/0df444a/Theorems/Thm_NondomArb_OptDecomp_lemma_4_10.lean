-- Prove2me | Theorems.Thm_NondomArb_OptDecomp_lemma_4_10
-- name    : NondomArb.OptDecomp.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:16:32.085304+00:00
-- url     : https://prove2.me/theorems/3dc592b5-77ed-4688-a2b9-2f6b9ba6d74c
-- title:
--   Lemma 4.10 — ℰ_t(f) = sup over 𝒬_t(ω) of E_Q[f(ω,·)] is upper semianalytic, with a measurable one-step superhedge y
-- statement:
--   Consider the nondominated market of §1.2 without options ($e = 0$). For $t \in \{0, \dots, T-1\}$ and $\omega \in \Omega_t$ let
--   $$\mathcal Q_t(\omega) = \{Q \in \mathfrak P(\Omega_1) : Q \lll \mathcal P_t(\omega),\ E_Q[\Delta S_{t+1}(\omega, \cdot)] = 0\}$$
--   be the one-period martingale measures, where $\Delta S_{t+1}(\omega, \cdot) = S_{t+1}(\omega, \cdot) - S_t(\omega)$.
--
--   **Lemma 4.10.** Let NA($\mathcal P$) hold, let $t \in \{0, \dots, T-1\}$ and let $f : \Omega_t \times \Omega_1 \to [-\infty, \infty]$ be upper semianalytic. Then
--   $$\mathcal E_t(f) : \Omega_t \to [-\infty, \infty], \qquad \mathcal E_t(f)(\omega) := \sup_{Q \in \mathcal Q_t(\omega)} E_Q[f(\omega, \cdot)]$$
--   is upper semianalytic. Moreover, there exists a universally measurable function $y : \Omega_t \to \mathbb R^d$ such that
--   $$\mathcal E_t(f)(\omega) + y(\omega) \Delta S_{t+1}(\omega, \cdot) \ge f(\omega, \cdot) \quad \mathcal P_t(\omega)\text{-q.s.} \tag{4.10}$$
--   for all $\omega \in \Omega_t$ such that NA($\mathcal P_t(\omega)$) holds and $f(\omega, \cdot) > -\infty$ $\mathcal P_t(\omega)$-q.s.
--
--   This is a measurable version of the one-period superhedging duality: the one-step superhedging price is the conditional sublinear expectation $\mathcal E_t(f)$, it stays upper semianalytic, and the hedge can be chosen measurably in the node $\omega$. In the optional decomposition it produces the strategy $H_{t+1} := y_t$.
--
--   **Formalization Note.** $E_Q$ is the extended expectation (1.1) and the supremum is taken in `EReal` (it is $-\infty$ when $\mathcal Q_t(\omega)$ is empty). The sum in (4.10) adds a real number to an extended real, so no $\infty - \infty$ arises. "$\mathcal P_t(\omega)$-q.s." means $P$-almost surely for every $P \in \mathcal P_t(\omega)$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 25, Lemma 4.10 (with 𝒬_t from Lemma 4.8, p. 22)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_OptDecomp_Model

open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.OptDecomp

/-- **Lemma 4.10** (Bouchard–Nutz, p. 25). In the market of §1.2 without options (`e = 0`), let
`NA(𝒫)` hold, let `t ∈ {0, …, T − 1}` and let `f : Ω_t × Ω₁ → [−∞, ∞]` be upper semianalytic.
Then `ℰ_t(f)(ω) = sup_{Q ∈ 𝒬_t(ω)} E_Q[f(ω, ·)]` is upper semianalytic, and there is a
universally measurable `y : Ω_t → ℝ^d` with
`ℰ_t(f)(ω) + y(ω) ΔS_{t+1}(ω, ·) ≥ f(ω, ·)` `𝒫_t(ω)`-q.s. (4.10) for every `ω ∈ Ω_t` such that
`NA(𝒫_t(ω))` holds and `f(ω, ·) > −∞` `𝒫_t(ω)`-q.s. -/
theorem lemma_4_10 {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁] [MeasurableSpace Ω₁]
    [BorelSpace Ω₁] {T d : ℕ} (M : Market Ω₁ T d 0) (hM : M.Standing) (hNA : M.NA)
    (t : ℕ) (ht : t < T) (f : (Fin t → Ω₁) × Ω₁ → EReal) (hf : NondomArb.Superhedge.IsUpperSemianalytic f) :
    NondomArb.Superhedge.IsUpperSemianalytic (M.condSup t f) ∧
      ∃ y : (Fin t → Ω₁) → (Fin d → ℝ), NondomArb.Superhedge.IsUMeasurable y ∧
        ∀ ω : Fin t → Ω₁, M.LocalNA t ω →
          (∀ P ∈ M.Pt t ω, ∀ᵐ x ∂(P : Measure Ω₁), ⊥ < f (ω, x)) →
          ∀ P ∈ M.Pt t ω, ∀ᵐ x ∂(P : Measure Ω₁),
            f (ω, x) ≤ M.condSup t f ω + ((y ω ⬝ᵥ M.incr t ω x : ℝ) : EReal) := by sorry

end NondomArb.OptDecomp
