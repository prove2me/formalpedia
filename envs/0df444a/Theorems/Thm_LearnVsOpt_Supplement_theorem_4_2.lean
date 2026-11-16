-- Prove2me | Theorems.Thm_LearnVsOpt_Supplement_theorem_4_2
-- name    : LearnVsOpt.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:21:57.334962+00:00
-- url     : https://prove2.me/theorems/5efdbd71-ce91-4c4c-afc4-1c6bb6b46342
-- title:
--   Theorem 4.2, p.10 — response-calibration error bounds the optimizer's gain, for any forecaster
-- statement:
--   Run Algorithm 1 (Forecast-Based Best-Response) with any randomized forecaster. In round $t$ the forecaster outputs a distribution $F_t$ over forecasts $f\in\Delta_{\hat n_O}$, and the learner responds to $f$ with $y(f)\in\mathrm{BR}_L(uc(f))$, chosen by a valid tie-breaking rule. Let $\mathcal T$ be the set of active rounds, $i_t$ the optimizer's actions, and
--   $$R_T=\sum_{t\in\mathcal T}\mathbb E_{f\sim F_t}\big[\delta^R(f,k_t)\big]$$
--   the response-calibration error (3)–(4). Then the optimizer's utility satisfies
--   $$\sum_{t\in\mathcal T}\mathbb E_{f\sim F_t}\big[e_{i_t}^\top U_O\,y(f)\big]\le \mathrm{BSE}\cdot|\mathcal T|+\sqrt{2n_O}\,n_L\,\|R_T\|_{L^2},$$
--   where $\mathrm{BSE}$ is the unbudgeted value (2) and $\|\cdot\|_{L^2}$ is the norm (5) over $[-1,1]$.
--
--   The bound holds pathwise, and indeed for every finite set of rounds $\mathcal T$, every family of forecast distributions and every sequence of optimizer actions.
--
--   This is the paper's bridge from calibration to non-manipulability: a forecaster with small response-calibration error leaves the optimizer at most $\mathrm{BSE}$ per active round, up to that error.
--
--   **Formalization Note** Forecast distributions are arbitrary probability measures on the forecast space, and the learner's response is assumed to be a measurable function of the forecast, so that the expectations are defined. $R_T$ is indexed by a duplicate-free enumeration of $\mathcal{UC}$.
--
--   Differences from the source:
--   - generalization: 𝒯 the active rounds of a run of Algorithm 1, F_t the forecaster's distributions and i_t the optimizer's actions in that run → any finite set of rounds 𝒯, any probability measures F_t on Δ_{n̂_O} for t ∈ 𝒯, and any actions i_t; reason: the inequality is pathwise and its proof is round by round; every run of Algorithm 1 with any forecaster is an instance
--   - generalization: any consistent tie-breaking rule (p.8) → every selector valid in the base's sense (IsValidSel), whose pure-response rule j₁ = j₂ → Q = 0 also admits j₁ ≠ j₂ with Q ∈ {0, 1}; reason: the paper's rule is a valid selector; the base mission's convention
--   - encoding: E_{f∼F_t}[·] for a distribution F_t over Δ_{n̂_O} → Bochner integral against F_t, with F_t a probability measure on ℕ → ℝ concentrated on IsForecast n̂_O, and the response f ↦ (j₁, j₂, Q, λ) measurable (SelMeasurable); reason: the expectation is defined only for a measurable response; the condition excludes only cases where the source's expression is undefined
--   - encoding: 𝒰𝒞 = {uc^(1), uc^(2), …}, k ∈ [n̂_O], k_t the index of uc_t → any duplicate-free enumeration D of 𝒰𝒞 (IsUCEnum); indices from 0; 1_{k_t=k} reads D[k] = uc_t; reason: the same objects; the norm does not depend on the order
--   - encoding: BSE = max in (2); the learner's null action j₀ with C_L[i, j₀] = 0 (§2) → Game.BSE ρ_L as sSup; hypothesis ∀ i, C_L i j₀ = 0; reason: the base's conventions; the set is nonempty and bounded
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Theorem 4.2, p.10 (PDF p.11); (3)–(5) pp.8–9

import Mathlib
import Definitions.Def_LearnVsOpt_BSE
import Definitions.Def_LearnVsOpt_Supplement_Forecaster

set_option autoImplicit false

open MeasureTheory
open scoped Matrix

namespace LearnVsOpt.Supplement

/-- **Theorem 4.2** (Fikioris, Sivan & Tardos, *Learning vs. Optimizing Players in Budgeted Games*,
arXiv:2611.05580, Theorem 4.2, p.10). Let `𝒯` be the set of active rounds of Algorithm 1, run with any
forecaster. Then the optimizer's utility is
`Σ_{t∈𝒯} E_{f∼F_t}[e_{i_t}⊤ U_O y(f)] ≤ BSE · |𝒯| + √(2n_O) n_L ‖R_T‖_{L²}`.

**Formalization Note.** The statement is pathwise: it holds for every finite set of rounds `𝒯`, every
family of forecast distributions `F_t` (arbitrary probability measures on `Δ_{n̂_O}`) and every sequence
of optimizer actions `i_t`, which contains every run of Algorithm 1 with any forecaster.
`R_T = Σ_{t∈𝒯} E_{f∼F_t}[δ^R(f, k_t)]` is indexed by a duplicate-free enumeration `D` of `𝒰𝒞`, and the
response `f ↦ (J⃗(f), Q(f), λ(f))` is assumed measurable so that the expectations are defined. BSE is the
unbudgeted value (2). -/
theorem theorem_4_2 {nO nL : ℕ} (G : Game nO nL) (ρL : ℝ) (hρ₀ : 0 < ρL) (hρ₁ : ρL ≤ 1)
    (j₀ : Fin nL) (hj₀ : ∀ i, G.CL i j₀ = 0) (sel : Selector nL) (hsel : IsValidSel j₀ ρL sel)
    (D : List (UC nL)) (hD : IsUCEnum G D) (hmeas : SelMeasurable sel D)
    (𝒯 : Finset ℕ) (F : ℕ → Measure Forecast)
    (hF : ∀ t ∈ 𝒯, IsProbabilityMeasure (F t) ∧ ∀ᵐ f ∂(F t), IsForecast G.nHat f)
    (i : ℕ → Fin nO) :
    ∑ t ∈ 𝒯, ∫ f, G.UO (i t) ⬝ᵥ (selAt sel D f).y ∂(F t) ≤
      G.BSE ρL * 𝒯.card + Real.sqrt (2 * nO) * nL *
        JointVec.normR G.nHat (sumJ 𝒯 fun t => expDelta ρL sel D (F t) (G.UL (i t), G.CL (i t))) := by sorry

end LearnVsOpt.Supplement
