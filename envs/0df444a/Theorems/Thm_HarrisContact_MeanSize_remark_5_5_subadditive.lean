-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_remark_5_5_subadditive
-- name    : HarrisContact.MeanSize.remark_5_5_subadditive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:24.321982+00:00
-- url     : https://prove2.me/theorems/287214b6-7066-484e-8ce0-30542ec38c1d
-- title:
--   Remark 5.5 with Theorem 5.6(b), p. 977 — if $\lambda_k\uparrow$ and $\lambda_k/k\downarrow$, $m_t$ is subadditive
-- statement:
--   Let $(\xi_t)$ be a contact process on $Z_d$ with death rate $\mu\ge0$ and birth rates $\lambda_0=0\le\lambda_1\le\dots\le\lambda_{2d}$ such that $\lambda_k/k$ is non-increasing for $1\le k\le 2d$. Then the expected size is subadditive: for all finite $\xi,\eta$ and $t\ge0$,
--   $$m_t(\xi\cup\eta)\le m_t(\xi)+m_t(\eta).$$
--
--   Theorem 5.6(b) states that under these conditions the process is subadditive, $p_t(\xi\cup\eta)\le p_t(\xi)+p_t(\eta)$, and Remark 5.5 notes that the coupling behind it gives the same inequality for $m_t$. The proof of Theorem 7.6 ends with this step: integrability of $m_t$ for singletons and pairs passes to every finite set.
--
--   **Formalization Note** The standing hypotheses of the contact process (Harris, §2(b), p. 971; §3, p. 972) are written as binders: $d \ge 1$, $\mu \ge 0$, $\lambda_0 = 0$ and $\lambda_k \ge 0$ for $0 \le k \le 2d$. Rates $\lambda_k$ with $k > 2d$ never enter the model, and no hypothesis mentions them. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$. The two monotonicity conditions range over $\{0,\dots,2d\}$ and $\{1,\dots,2d\}$ respectively. The paper notes on p. 978 that $\lambda_k\uparrow$ and $\lambda_k\le k\lambda_1$ alone do not give subadditivity of $m_t$ for $d=2$, so the condition $\lambda_k/k\downarrow$ is essential.
-- source:
--   Harris (Ann. Probab. 2, 1974), Remark 5.5 and Theorem 5.6(b), p. 977; (5.3), p. 976

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Remark 5.5, p. 977, with Theorem 5.6(b): if `λ_k ↑` and `λ_k/k ↓`
(`k ≥ 1`) then `m_t` is subadditive: `m_t(ξ ∪ η) ≤ m_t(ξ) + m_t(η)`. -/
theorem remark_5_5_subadditive {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hmono : MonotoneOn lam (Set.Iic (2 * d)))
    (hanti : AntitoneOn (fun k : ℕ => lam k / k) (Set.Icc 1 (2 * d))) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ η : HarrisContact.Extinction.Config d,
      HarrisContact.Extinction.meanSize μ lam t (ξ ∪ η) ≤ HarrisContact.Extinction.meanSize μ lam t ξ + HarrisContact.Extinction.meanSize μ lam t η := by sorry
end HarrisContact.MeanSize
