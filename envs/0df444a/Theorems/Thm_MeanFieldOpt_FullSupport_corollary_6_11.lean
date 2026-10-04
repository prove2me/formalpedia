-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_corollary_6_11
-- name    : MeanFieldOpt.FullSupport.corollary_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:11:11.050408+00:00
-- url     : https://prove2.me/theorems/53c830b5-0054-43f8-9830-7ef43f36f86b
-- title:
--   Corollary 6.11 — $\xi''(t)\,\mathbb E\{\partial_x^2\Phi^{\gamma_*}(t,X_t)^2\}=1$ on $\overline S(\gamma_*)$
-- statement:
--   Let $\xi$ be a mixture that is not identically zero, $f_0$ an admissible terminal condition, and $\mathsf P$ the Parisi functional with terminal condition $f_0$. Assume $\gamma_* \in \mathscr L$ (right-continuous on $[0,1)$) satisfies $\mathsf P(\gamma_*) = \inf_{\gamma \in \mathscr L} \mathsf P(\gamma)$, and let $X$ be the strong solution of the SDE (6.3) for $\gamma_*$, driven by a standard Brownian motion. Then
--
--   $$
--   t \in \overline S(\gamma_*) \;\Rightarrow\; \xi''(t)\,\mathbb E\{\partial_x^2\Phi^{\gamma_*}(t, X_t)^2\} = 1 .
--   $$
--
--   This second-order stationarity condition is one of the two identities used at the endpoints of a gap of the support in the proof of the main theorem.
--
--   **Formalization Note** Minimality is $\mathsf P(\gamma_*) \le \mathsf P(\gamma)$ for all $\gamma \in \mathscr L$. The hypothesis that some $c_k \neq 0$ is added: for $\xi \equiv 0$, $\gamma_* \equiv 1$ is a minimizer with $\overline S(\gamma_*) = [0,1)$ while $\xi'' \equiv 0$, so the left side is $0 \ne 1$. When $c_2 = 0$ (so $\xi''(0) = 0$) the statement at $t = 0$ forces $0 \notin \overline S(\gamma_*)$; together with the main theorem it shows that no minimizer exists in that case, as in the paper.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 29, Corollary 6.11

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiP
import Definitions.Def_MeanFieldOpt_FullSupport_Support
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiSDE

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MeanFieldOpt.FullSupport

/-- Corollary 6.11 (arXiv:2001.00904v1, p. 29): if `γ_* ∈ ℒ` attains `inf_{γ ∈ ℒ} P(γ)`, then
`ξ''(t) E{∂²_xΦ^{γ_*}(t, X_t)²} = 1` for `t ∈ S̄(γ_*)`.
Added (disclosed) hypothesis: the mixture is not identically zero. -/
theorem corollary_6_11 (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0) (f₀ : ℝ → ℝ) (hf₀ : IsTerminal f₀)
    (γs : ℝ → ℝ) (hγs : InL ξ γs)
    (hrc : ∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt γs (Set.Ici t) t)
    (hmin : ∀ γ : ℝ → ℝ, InL ξ γ → ParisiP ξ f₀ γs ≤ ParisiP ξ f₀ γ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W X : ℝ≥0 → Ω → EthierKurtz.SDEState 1) (hW : IsBrownianReal (fun t ω => W t ω 0) P)
    (hX : IsParisiSDESol ξ f₀ γs P W X) :
    ∀ t ∈ closure (S γs) ∩ Set.Ico 0 1,
      ξ.d2 t * ∫ ω, (deriv (deriv (PhiL ξ f₀ γs t)) (pathAt X t ω)) ^ 2 ∂P = 1 := by sorry

end MeanFieldOpt.FullSupport
