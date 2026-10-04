-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_theorem_5
-- name    : MeanFieldOpt.FullSupport.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:10:03.546723+00:00
-- url     : https://prove2.me/theorems/ada5324c-c798-4dd4-8398-a7bfc673ca72
-- title:
--   Theorem 5 — every minimizer of the extended Parisi functional has full support $\overline S(\gamma_*)=[0,1)$
-- statement:
--   Let $\xi(t) = \sum_{k\ge2} c_k^2 t^k$ be a mixture with $\xi(1+\varepsilon) < \infty$ for some $\varepsilon > 0$, not identically zero. Consider the Parisi functional with terminal condition $f_0(x) = |x|$,
--
--   $$
--   \mathsf P(\gamma) = \Phi^\gamma(0,0) - \frac12 \int_0^1 t\,\xi''(t)\gamma(t)\,dt, \qquad \gamma \in \mathscr L,
--   $$
--
--   where $\Phi^\gamma$ solves the Parisi PDE $\partial_t\Phi + \frac12\xi''(t)(\partial_x^2\Phi + \gamma(t)(\partial_x\Phi)^2) = 0$, $\Phi(1,x) = |x|$. Assume $\gamma_* \in \mathscr L$ (right-continuous on $[0,1)$) satisfies $\mathsf P(\gamma_*) = \inf_{\gamma \in \mathscr L} \mathsf P(\gamma)$. Then
--
--   $$
--   \overline S(\gamma_*) = [0,1),
--   $$
--
--   where $\overline S(\gamma_*)$ is the closure in $[0,1)$ of $\{t \in [0,1) : \gamma_*(t) > 0\}$.
--
--   In words: a minimizer of the extended variational principle cannot vanish on any interval. This is what makes the optimal incremental message passing algorithm of the paper well defined on the whole time interval.
--
--   **Formalization Note** Minimality is stated as $\mathsf P(\gamma_*) \le \mathsf P(\gamma)$ for every $\gamma \in \mathscr L$ (not via the real infimum, which is $0$ on unbounded sets). The closure in $[0,1)$ is `closure (S γ) ∩ Set.Ico 0 1`. Right-continuity of $\gamma_*$ is the paper's standing convention from p. 28. The hypothesis that some $c_k \ne 0$ is added: for $\xi \equiv 0$, $\Phi^\gamma(t,x) = |x|$ and $\mathsf P \equiv 0$ on $\mathscr L$, so $\gamma_* \equiv 0$ is a minimizer with empty support. When $c_2 = 0$, Corollary 6.11 at $t=0$ shows that no minimizer exists, and the statement holds vacuously, as in the paper.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 30, Theorem 5

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiP
import Definitions.Def_MeanFieldOpt_FullSupport_Support

namespace MeanFieldOpt.FullSupport

/-- Theorem 5 (arXiv:2001.00904v1, p. 30): with `f₀(x) = |x|`, if `γ_* ∈ ℒ` (right-continuous, the
paper's convention from p. 28) attains `inf_{γ ∈ ℒ} P(γ)`, then `S̄(γ_*) = [0,1)`.
Added (disclosed) hypothesis: the mixture is not identically zero. -/
theorem theorem_5 (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0) (γs : ℝ → ℝ) (hγs : InL ξ γs)
    (hrc : ∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt γs (Set.Ici t) t)
    (hmin : ∀ γ : ℝ → ℝ, InL ξ γ → ParisiP ξ (fun x => |x|) γs ≤ ParisiP ξ (fun x => |x|) γ) :
    closure (S γs) ∩ Set.Ico 0 1 = Set.Ico 0 1 := by sorry

end MeanFieldOpt.FullSupport
