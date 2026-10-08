-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_remark_5_5_increasing
-- name    : HarrisContact.MeanSize.remark_5_5_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:35.284453+00:00
-- url     : https://prove2.me/theorems/f6d38785-abc9-43b4-83a0-c07c9b3395f4
-- title:
--   Remark 5.5 with Theorem 5.6(a), p. 977 — if $\lambda_k\uparrow$, $m_t(\xi)$ is increasing in $\xi$
-- statement:
--   Let $(\xi_t)$ be a contact process on $Z_d$ with death rate $\mu\ge0$ and birth rates $\lambda_0=0\le\lambda_1\le\dots\le\lambda_{2d}$. Then the expected size is increasing in the initial set: for all finite $\xi,\eta$ and $t\ge0$,
--   $$m_t(\xi)\le m_t(\xi\cup\eta).$$
--
--   Theorem 5.6(a) states that $\lambda_k\uparrow$ makes the process increasing, and Remark 5.5 notes that the coupling proving it ($\xi_t\subset\xi'_t$ with $\xi_0=\xi$, $\xi'_0=\xi\cup\eta$) makes $m_t(\xi)$ increasing as well. In the proof of Theorem 7.6 this guarantees $m_t(\xi)-m_t\ge0$ in Lemma 7.5.
--
--   **Formalization Note** The standing hypotheses of the contact process (Harris, §2(b), p. 971; §3, p. 972) are written as binders: $d \ge 1$, $\mu \ge 0$, $\lambda_0 = 0$ and $\lambda_k \ge 0$ for $0 \le k \le 2d$. Rates $\lambda_k$ with $k > 2d$ never enter the model, and no hypothesis mentions them. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$. "$\lambda_k\uparrow$" is monotonicity of $k\mapsto\lambda_k$ on $\{0,\dots,2d\}$. The paper's remark concerns all $\xi,\eta\in\Xi$; it is drafted for finite sets.
-- source:
--   Harris (Ann. Probab. 2, 1974), Remark 5.5 and Theorem 5.6(a), p. 977; (5.2), p. 976

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Remark 5.5, p. 977, with Theorem 5.6(a): if `λ_k ↑` then `m_t(ξ)` is
increasing in `ξ`: `m_t(ξ) ≤ m_t(ξ ∪ η)`. -/
theorem remark_5_5_increasing {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hmono : MonotoneOn lam (Set.Iic (2 * d))) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ η : HarrisContact.Extinction.Config d, HarrisContact.Extinction.meanSize μ lam t ξ ≤ HarrisContact.Extinction.meanSize μ lam t (ξ ∪ η) := by sorry
end HarrisContact.MeanSize
