-- Prove2me | Theorems.Thm_NonsmoothQN_LineSearch_terminates_of_weakly_lower_semismooth
-- name    : NonsmoothQN.LineSearch.terminates_of_weakly_lower_semismooth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:58.11553+00:00
-- url     : https://prove2.me/theorems/bdbdec23-1e1d-42aa-88e8-970c2429f9fd
-- title:
--   §4.1, pp. 148–149 — weakly lower semismooth h, differentiable at every trial ⇒ the line search terminates
-- statement:
--   Let $h$ satisfy Assumption 4.1 with slope $s<0$ and let $0<c_1<c_2<1$. Suppose that $h$ is weakly lower semismooth at every $\bar t>0$: it is locally Lipschitz around $\bar t$ and, for $d=\pm1$ and every sequence $\tau_k\downarrow0$ such that $h$ is differentiable at $\bar t+\tau_kd$,
--   $$\liminf_{\tau\downarrow0}\frac{h(\bar t+\tau d)-h(\bar t)}{\tau}\ \ge\ \limsup_k h'(\bar t+\tau_kd)\,d .$$
--   Suppose also that $h$ is differentiable at every trial step of Algorithm 4.6. Then Algorithm 4.6 terminates.
--
--   This extends the termination guarantee of Theorem 4.7 beyond condition (4.8) to the class of functions for which Lemaréchal's line search is usually analysed.
--
--   **Formalization Note.** The paper quantifies over arbitrary subgradients $g_k$ of $h$ at $\bar t+\tau_kd$. Since the Clarke subdifferential is not available, the condition here only involves derivatives at points of differentiability (these are subgradients), which is the case the paper's argument uses ($g_k=h'(\alpha_k)$). The hypothesis is therefore weaker than the paper's, and the statement stronger; the paper's argument proves it unchanged.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, pp. 148–149, §4.1, remark after the proof of Theorem 4.7

import Mathlib
import Definitions.Def_NonsmoothQN_LineSearch_Basic

open Filter Topology MeasureTheory Set

namespace NonsmoothQN.LineSearch

/-- §4.1, pp. 148–149. Under Assumption 4.1 with `0 < c₁ < c₂ < 1`, if `h` is weakly lower
semismooth at every `t̄ > 0` (subgradients restricted to derivatives at points of
differentiability) and `h` is differentiable at every trial step, then Algorithm 4.6
terminates. -/
theorem terminates_of_weakly_lower_semismooth (h : ℝ → ℝ) (c₁ c₂ s : ℝ)
    (hA41 : Assumption41 h s) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1)
    (hwlss : ∀ tbar : ℝ, 0 < tbar → WeaklyLowerSemismoothDeriv h tbar)
    (hdiff : ∀ n : ℕ, DifferentiableAt ℝ h (lsRun h c₁ c₂ s n).t) :
    Terminates h c₁ c₂ s := by sorry

end NonsmoothQN.LineSearch
