-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_corollary_6_10
-- name    : MeanFieldOpt.FullSupport.corollary_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:10:59.177714+00:00
-- url     : https://prove2.me/theorems/aa74da20-1446-4347-8fa8-eba553016623
-- title:
--   Corollary 6.10 — stationarity: $\mathbb E\{\partial_x\Phi^{\gamma_*}(t,X_t)^2\}=t$ on $\overline S(\gamma_*)$, $\ge t$ off it
-- statement:
--   Let $\xi$ be a mixture that is not identically zero, $f_0$ an admissible terminal condition, and $\mathsf P$ the Parisi functional with terminal condition $f_0$. Assume $\gamma_* \in \mathscr L$ (right-continuous on $[0,1)$) satisfies $\mathsf P(\gamma_*) = \inf_{\gamma \in \mathscr L} \mathsf P(\gamma)$. Let $X$ be the strong solution of the SDE (6.3) for $\gamma_*$, driven by a standard Brownian motion. Then
--
--   $$
--   t \in \overline S(\gamma_*) \;\Rightarrow\; \mathbb E\{\partial_x\Phi^{\gamma_*}(t, X_t)^2\} = t, \qquad
--   t \in [0,1) \setminus \overline S(\gamma_*) \;\Rightarrow\; \mathbb E\{\partial_x\Phi^{\gamma_*}(t, X_t)^2\} \ge t .
--   $$
--
--   These are the first-order optimality conditions of the extended variational principle.
--
--   **Formalization Note** "$\gamma_*$ attains the infimum" is stated as $\mathsf P(\gamma_*) \le \mathsf P(\gamma)$ for every $\gamma \in \mathscr L$, which avoids a junk value of the real infimum. The hypothesis that some $c_k \ne 0$ is added: for $\xi \equiv 0$, $X \equiv 0$ and $\Phi^\gamma = f_0$ for every $\gamma$, so $\gamma_* \equiv 1$ is a minimizer with $\overline S(\gamma_*) = [0,1)$ and $\mathbb E\{\partial_x\Phi(t,X_t)^2\} = f_0'(0)^2$ constant in $t$, contradicting "$= t$". The paper's proof uses $\xi''(t) > 0$ on $(0,1)$, which holds exactly when $\xi \not\equiv 0$. Right-continuity is the paper's convention from p. 28.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 28, Corollary 6.10, Eqs. (6.13)–(6.14)

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiP
import Definitions.Def_MeanFieldOpt_FullSupport_Support
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiSDE

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MeanFieldOpt.FullSupport

/-- Corollary 6.10 (arXiv:2001.00904v1, p. 28): if `γ_* ∈ ℒ` attains `inf_{γ ∈ ℒ} P(γ)`, then
`E{∂_xΦ^{γ_*}(t, X_t)²} = t` for `t ∈ S̄(γ_*)` and `≥ t` for `t ∈ [0,1) \ S̄(γ_*)`.
Added (disclosed) hypothesis: the mixture is not identically zero. -/
theorem corollary_6_10 (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0) (f₀ : ℝ → ℝ) (hf₀ : IsTerminal f₀)
    (γs : ℝ → ℝ) (hγs : InL ξ γs)
    (hrc : ∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt γs (Set.Ici t) t)
    (hmin : ∀ γ : ℝ → ℝ, InL ξ γ → ParisiP ξ f₀ γs ≤ ParisiP ξ f₀ γ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W X : ℝ≥0 → Ω → EthierKurtz.SDEState 1) (hW : IsBrownianReal (fun t ω => W t ω 0) P)
    (hX : IsParisiSDESol ξ f₀ γs P W X) :
    (∀ t ∈ closure (S γs) ∩ Set.Ico 0 1,
      ∫ ω, (deriv (PhiL ξ f₀ γs t) (pathAt X t ω)) ^ 2 ∂P = t) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1 \ (closure (S γs) ∩ Set.Ico 0 1),
      t ≤ ∫ ω, (deriv (PhiL ξ f₀ γs t) (pathAt X t ω)) ^ 2 ∂P) := by sorry

end MeanFieldOpt.FullSupport
