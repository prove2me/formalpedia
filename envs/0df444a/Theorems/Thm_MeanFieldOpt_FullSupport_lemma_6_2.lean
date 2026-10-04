-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_lemma_6_2
-- name    : MeanFieldOpt.FullSupport.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:47:36.787973+00:00
-- url     : https://prove2.me/theorems/b3886289-1c33-45d0-b26a-89587a598a4e
-- title:
--   Lemma 6.2 — $\Phi^\gamma(t,\cdot)$ is convex and 1-Lipschitz, and $\partial_x\Phi^{\gamma_n}\to\partial_x\Phi^\gamma$ a.e.
-- statement:
--   Let $\xi$ be a mixture, $f_0$ an admissible terminal condition and $\gamma \in \mathscr L$. Then:
--
--   1. for every $t \in [0,1]$ the function $x \mapsto \Phi^\gamma(t,x)$ is convex and $1$-Lipschitz; equivalently, $\partial_x\Phi^\gamma$ exists in the weak sense, is non-decreasing, and $|\partial_x\Phi^\gamma(t,x)| \le 1$;
--   2. if $\gamma_n \in \mathsf{SF}_+$ and $\int_0^1 \xi''(s)|\gamma_n(s) - \gamma(s)|\,ds \to 0$, then for every $t \in [0,1]$,
--   $$
--   \partial_x\Phi^{\gamma_n}(t,x) \longrightarrow \partial_x\Phi^\gamma(t,x) \qquad \text{for almost every } x \in \mathbb R .
--   $$
--
--   These properties carry the gradient bound of Proposition 6.1 from step functions to all of $\mathscr L$.
--
--   **Formalization Note** The paper's first claim ("$\partial_x\Phi^\gamma$ exists in weak sense, is non-decreasing, and bounded by $1$") is stated in the equivalent form "convex and 1-Lipschitz", which avoids weak derivatives. In the second claim derivatives are Lean's `deriv`; the convergence is with respect to Lebesgue measure. The paper's third claim, the weak formulation (6.4), is not part of this item: it is printed with a boundary term $\int\Phi(1,x)f_0(x)\,dx$ that does not involve the test function.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 24, Lemma 6.2 (first two sentences)

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_PhiL

open MeasureTheory Filter Topology

namespace MeanFieldOpt.FullSupport

/-- Lemma 6.2, first two claims (arXiv:2001.00904v1, p. 24): for `γ ∈ ℒ`, `Φ^γ(t, ·)` is convex
and 1-Lipschitz for every `t ∈ [0,1]` (equivalently: `∂_xΦ^γ` exists in the weak sense, is
non-decreasing and bounded by `1`); and if `γ_n ∈ SF₊`, `γ_n → γ` in `L¹_ξ`, then for every
`t ∈ [0,1]`, `∂_xΦ^{γ_n}(t, x) → ∂_xΦ^γ(t, x)` for almost every `x`. -/
theorem lemma_6_2 (ξ : Mixture) (f₀ : ℝ → ℝ) (hf₀ : IsTerminal f₀) (γ : ℝ → ℝ)
    (hγ : InL ξ γ) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      ConvexOn ℝ Set.univ (PhiL ξ f₀ γ t) ∧ LipschitzWith 1 (PhiL ξ f₀ γ t)) ∧
    ∀ γn : ℕ → SFData,
      Tendsto (fun n => ∫ s in Set.Ico (0 : ℝ) 1, ξ.d2 s * |(γn n).toFun s - γ s|) atTop (𝓝 0) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ x ∂(volume : Measure ℝ),
        Tendsto (fun n => deriv (PhiSF ξ f₀ (γn n) t) x) atTop
          (𝓝 (deriv (PhiL ξ f₀ γ t) x)) := by sorry

end MeanFieldOpt.FullSupport
