-- Prove2me | Theorems.Thm_LearnVsOpt_Supplement_theorem_5_2
-- name    : LearnVsOpt.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:22:25.873903+00:00
-- url     : https://prove2.me/theorems/89a487c7-8838-4961-b984-1274d2f91bd1
-- title:
--   Theorem 5.2, p.14 — Lagrangian-calibration error bounds the interval stochastic regret, for any forecaster
-- statement:
--   Run Algorithm 1 with any randomized forecaster against any adaptive optimizer, for $T\ge1$ rounds. Let $\mathcal I=\{t_1+1,\dots,t_2\}\subseteq[T]$ be a contiguous interval of rounds in which the optimizer draws $i_t\sim x$ independently in each round $t\in\mathcal I$, for some $x\in\Delta_{n_O}$, and let $y^\star\in\mathrm{BR}_L(x)$. Let $L_t$ be the Lagrangian-calibration error of p.12. Then, regardless of the optimizer's play outside $\mathcal I$,
--   $$\mathbb E\Big[\sum_{t\in\mathcal I}U_L[i_t,j_t]\Big]\ \ge\ |\mathcal I|\cdot x^\top U_L y^\star-\frac{14\sqrt{n_L}}{\rho_L}\,\mathbb E\Big[\max_{t\le T}\|L_t\|_2\Big]-\frac{2\sqrt T+1}{\rho_L}.$$
--
--   This is the paper's bridge from calibration to low stochastic regret. It applies to every forecaster, so a forecaster with small Lagrangian-calibration error makes the learner nearly best-respond on every stationary interval.
--
--   **Formalization Note** The forecaster and the optimizer are Markov kernels from the history. The learner samples $j_t\sim y(f^{(t)})$ through a kernel $\eta$, and its response is measurable in the forecast. The expectation is over the law of play `playLaw`, and the maximum is over $t\in\{1,\dots,T\}$.
--
--   Differences from the source:
--   - generalization: a forecaster that receives the reported uc_t (Algorithm 1, p.7) → any Markov kernel F_t from the whole history (past i_r, f^(r), j_r) to probability measures on Δ_{n̂_O}; reason: a larger class; every forecaster of the paper is an instance, and the theorem is stated for any forecaster (§3, p.7)
--   - generalization: an adaptive optimizer, stationary on 𝓘 and arbitrary outside → any Markov kernel σ_t from the whole history, including past forecasts, to [n_O], with σ_{t−1}(h) = x for every history h before a round t ∈ 𝓘; reason: an optimizer that sees less is an instance; the current round's f^(t) and j_t stay unseen (simultaneous moves)
--   - generalization: any consistent tie-breaking rule (p.8) → every valid selector (IsValidSel); reason: as in the base mission; the paper's rule is an instance
--   - encoding: E_{f∼F_t}[·] and sampling j_t ∼ y(f^(t)) → Bochner integrals with a measurable response (SelMeasurable), and a Markov kernel η with η(f){j} = y(f)_j for every forecast f; reason: such an η exists exactly when y is measurable; this only excludes cases where the source's expectations are undefined
--   - encoding: the probability space of the repeated game; T rounds; max_{t≤T} → playLaw, built round by round with Measure.compProd and Kernel products; histories Fin T → Rec with round t at position t − 1; non-active rounds record the forecast 0; max over t ∈ {1, …, T} with T ≥ 1; reason: Lean representation of the same law
--   - encoding: 𝒰𝒞 indexed by k ∈ [n̂_O]; the null action j₀ (§2) → a duplicate-free enumeration D of 𝒰𝒞; hypothesis ∀ i, C_L i j₀ = 0; reason: the same objects
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Theorem 5.2, p.14 (PDF p.15); L_t p.12

import Mathlib
import Definitions.Def_LearnVsOpt_Play
import Definitions.Def_LearnVsOpt_Supplement_Play

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace LearnVsOpt.Supplement

/-- **Theorem 5.2** (Fikioris, Sivan & Tardos, *Learning vs. Optimizing Players in Budgeted Games*,
arXiv:2611.05580, Theorem 5.2, p.14). Run Algorithm 1 with any forecaster. Let
`I = {t₁ + 1, …, t₂} ⊆ [T]` be any contiguous interval of rounds in which the optimizer draws `i_t ∼ x`
independently in each round, for some `x ∈ Δ_{n_O}`, and let `y⋆ ∈ BR_L(x)`. Then, regardless of the
optimizer's play outside `I`,
`E[Σ_{t∈I} U_L[i_t, j_t]] ≥ |I| · x⊤U_L y⋆ − (14√n_L/ρ_L) E[max_{t≤T} ‖L_t‖₂] − (2√T + 1)/ρ_L`.

**Formalization Note.** The forecaster is any kernel `F_t` from the history to probability measures on
`Δ_{n̂_O}`; the optimizer is any kernel `σ_t` from the history to `Δ_{n_O}`; both may read the whole past
(the optimizer not the current round). `η` samples `j ∼ y(f)`. The maximum is over `t ∈ {1, …, T}`. -/
theorem theorem_5_2 {nO nL : ℕ} (G : Game nO nL) (ρL : ℝ) (hρ₀ : 0 < ρL) (hρ₁ : ρL ≤ 1)
    (j₀ : Fin nL) (hj₀ : ∀ i, G.CL i j₀ = 0) (sel : Selector nL) (hsel : IsValidSel j₀ ρL sel)
    (D : List (UC nL)) (hD : IsUCEnum G D) (hmeas : SelMeasurable sel D)
    (F : (t : ℕ) → Kernel (Hist nO nL t) Forecast) [∀ t, IsMarkovKernel (F t)]
    (hF : ∀ (t : ℕ) (h : Hist nO nL t), ∀ᵐ f ∂(F t h), IsForecast G.nHat f)
    (η : Kernel Forecast (Fin nL)) [IsMarkovKernel η]
    (hη : ∀ f : Forecast, IsForecast G.nHat f → ∀ j, (η f {j}).toReal = (selAt sel D f).y j)
    (σ : (t : ℕ) → Kernel (Hist nO nL t) (Fin nO)) [∀ t, IsMarkovKernel (σ t)]
    (T : ℕ) (hT : 1 ≤ T) (t₁ t₂ : ℕ) (ht : t₂ ≤ T) (x : Fin nO → ℝ) (hx : x ∈ stdSimplex ℝ (Fin nO))
    (hσ : ∀ t ∈ Finset.Ioc t₁ t₂, ∀ (h : Hist nO nL (t - 1)) (i : Fin nO),
      (σ (t - 1) h {i}).toReal = x i)
    (yS : Fin nL → ℝ) (hy : yS ∈ G.BRx ρL x) :
    ((Finset.Ioc t₁ t₂).card : ℝ) * (x ⬝ᵥ (G.UL *ᵥ yS)) -
        14 * Real.sqrt nL / ρL *
          ∫ h, maxRounds T hT (fun t => JointVec.normL (Lvec G ρL sel D F h t))
            ∂(playLaw G ρL j₀ σ F η T) -
        (2 * Real.sqrt T + 1) / ρL ≤
      ∫ h, ∑ t ∈ Finset.Ioc t₁ t₂, entry h G.UL t ∂(playLaw G ρL j₀ σ F η T) := by sorry

end LearnVsOpt.Supplement
