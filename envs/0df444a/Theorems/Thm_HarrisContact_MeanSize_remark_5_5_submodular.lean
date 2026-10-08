-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_remark_5_5_submodular
-- name    : HarrisContact.MeanSize.remark_5_5_submodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:25.812009+00:00
-- url     : https://prove2.me/theorems/bbbbe773-9d35-4f50-90d2-f4f49cb18820
-- title:
--   Remark 5.5 with Theorem 6.2, pp. 977–979 — for concave non-decreasing $\lambda$, $m_t$ is submodular
-- statement:
--   Let $(\xi_t)$ be a contact process on $Z_d$ with death rate $\mu\ge0$ and birth rates $\lambda_0=0,\lambda_1,\dots,\lambda_{2d}$ that are non-decreasing and concave in $i$, i.e. $\lambda_{i+2}-\lambda_{i+1}\le\lambda_{i+1}-\lambda_i$ for $0\le i\le 2d-2$. Then the expected size is submodular: for all finite $\xi,\eta$ and $t\ge0$,
--   $$m_t(\xi\cup\eta)+m_t(\xi\cap\eta)\le m_t(\xi)+m_t(\eta).$$
--
--   Theorem 6.2 proves this inequality for $p_t$, and Remark 5.5 says the same coupling argument applies to (5.4) for $m_t$. The proof of Theorem 7.6 uses it at (7.8) for the linear rates $\lambda_k=k\lambda$ to bound $m_{t-s}(\xi\cup x)$ for a pair $\xi$ of neighbours.
--
--   **Formalization Note** The standing hypotheses of the contact process (Harris, §2(b), p. 971; §3, p. 972) are written as binders: $d \ge 1$, $\mu \ge 0$, $\lambda_0 = 0$ and $\lambda_k \ge 0$ for $0 \le k \le 2d$. Rates $\lambda_k$ with $k > 2d$ never enter the model, and no hypothesis mentions them. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$. Concavity and monotonicity are imposed on $\{\lambda_i: 0\le i\le 2d\}$, as in §6 (p. 979). Drafted for finite $\xi,\eta$.
-- source:
--   Harris (Ann. Probab. 2, 1974), Remark 5.5, p. 977; (5.4), p. 976; Theorem 6.2, p. 979; used at (7.8), p. 982

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Remark 5.5, p. 977, with Theorem 6.2, p. 979, as used at (7.8), p. 982:
if `{λ_i : 0 ≤ i ≤ 2d}` is concave and non-decreasing with `λ_0 = 0`, then `m_t` is submodular:
`m_t(ξ ∪ η) + m_t(ξ ∩ η) ≤ m_t(ξ) + m_t(η)`. -/
theorem remark_5_5_submodular {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hmono : MonotoneOn lam (Set.Iic (2 * d)))
    (hconc : ∀ i, i + 2 ≤ 2 * d → lam (i + 2) - lam (i + 1) ≤ lam (i + 1) - lam i) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ η : HarrisContact.Extinction.Config d,
      HarrisContact.Extinction.meanSize μ lam t (ξ ∪ η) + HarrisContact.Extinction.meanSize μ lam t (ξ ∩ η) ≤ HarrisContact.Extinction.meanSize μ lam t ξ + HarrisContact.Extinction.meanSize μ lam t η := by sorry
end HarrisContact.MeanSize
