-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_corollary_6_6
-- name    : MeanFieldOpt.FullSupport.corollary_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:10:20.938268+00:00
-- url     : https://prove2.me/theorems/dbfef458-9336-4fbc-b643-e873152ac498
-- title:
--   Corollary 6.6 — $\frac{d}{dt}\mathbb E\{\partial_x\Phi(t,X_t)^2\}=\xi''(t)\mathbb E\{(\partial_x^2\Phi(t,X_t))^2\}$
-- statement:
--   Let $\xi$ be a mixture, $f_0$ an admissible terminal condition, $\gamma \in \mathscr L$, $\Phi = \Phi^\gamma$, and let $X$ be the strong solution of the SDE (6.3) driven by a standard Brownian motion. For all $0 \le t_1 < t_2 < 1$,
--
--   $$
--   \mathbb E\{\partial_x\Phi(t_2, X_{t_2})^2\} - \mathbb E\{\partial_x\Phi(t_1, X_{t_1})^2\} = \int_{t_1}^{t_2} \xi''(s)\, \mathbb E\{(\partial_x^2\Phi(s, X_s))^2\}\,ds .
--   $$
--
--   In particular, $t \mapsto \mathbb E\{\partial_x\Phi(t, X_t)^2\}$ is Lipschitz continuous on $[0, 1-\varepsilon)$ for every $\varepsilon > 0$.
--
--   This identity links the two expectations appearing in the stationarity conditions of Corollaries 6.10 and 6.11.
--
--   **Formalization Note** $\partial_x\Phi$ and $\partial_x^2\Phi$ are iterated `deriv`s of $x \mapsto \Phi^\gamma(t,x)$; expectations are Bochner integrals, with integrands that are bounded for $t<1$ (by Proposition 6.1(b) and the regularity Lemma 6.4 of the paper). The theorem holds for every strong solution $X$, which by Lemma 6.5 is the paper's process.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 27, Corollary 6.6

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiSDE

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MeanFieldOpt.FullSupport

/-- Corollary 6.6 (arXiv:2001.00904v1, p. 27): for `γ ∈ ℒ` and `0 ≤ t₁ < t₂ < 1`,
`E{∂_xΦ(t₂, X_{t₂})²} - E{∂_xΦ(t₁, X_{t₁})²} = ∫_{t₁}^{t₂} ξ''(s) E{(∂²_xΦ(s, X_s))²} ds`; in
particular `t ↦ E{∂_xΦ(t, X_t)²}` is Lipschitz continuous on `[0, 1 - ε)` for any `ε > 0`. -/
theorem corollary_6_6 (ξ : Mixture) (f₀ : ℝ → ℝ) (hf₀ : IsTerminal f₀) (γ : ℝ → ℝ)
    (hγ : InL ξ γ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W X : ℝ≥0 → Ω → EthierKurtz.SDEState 1) (hW : IsBrownianReal (fun t ω => W t ω 0) P)
    (hX : IsParisiSDESol ξ f₀ γ P W X) :
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ < 1 →
      (∫ ω, (deriv (PhiL ξ f₀ γ t₂) (pathAt X t₂ ω)) ^ 2 ∂P) -
          (∫ ω, (deriv (PhiL ξ f₀ γ t₁) (pathAt X t₁ ω)) ^ 2 ∂P) =
        ∫ s in t₁..t₂, ξ.d2 s * ∫ ω, (deriv (deriv (PhiL ξ f₀ γ s)) (pathAt X s ω)) ^ 2 ∂P) ∧
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0,
      LipschitzOnWith K (fun t => ∫ ω, (deriv (PhiL ξ f₀ γ t) (pathAt X t ω)) ^ 2 ∂P)
        (Set.Ico 0 (1 - ε)) := by sorry

end MeanFieldOpt.FullSupport
