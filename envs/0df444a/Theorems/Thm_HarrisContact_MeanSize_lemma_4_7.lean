-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_lemma_4_7
-- name    : HarrisContact.MeanSize.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:36.938751+00:00
-- url     : https://prove2.me/theorems/265295dc-9105-4e48-ae86-bbb06f13c914
-- title:
--   Lemma 4.7, p. 975 — $m_t(\xi) \le |\xi|\,e^{(2d\Lambda-\mu)t}$
-- statement:
--   Let $(\xi_t)$ be the contact process on $Z_d$ with death rate $\mu\ge0$ and birth rates $\lambda_0=0,\lambda_1,\dots,\lambda_{2d}\ge0$, and let $m_t(\xi)$ be the expected number of occupied sites at time $t$ when the process starts from the finite set $\xi$. Put $\Lambda=\max_{0\le i\le 2d}\lambda_i$. Then for every finite $\xi$ and every $t\ge 0$,
--   $$m_t(\xi)\le |\xi|\,e^{(2d\Lambda-\mu)t}.$$
--
--   This crude bound shows in particular that $m_t(\xi)$ is finite and bounded on every finite time interval, which is what makes the integrals of $m_t$ in the proof of Theorem 7.6 meaningful.
--
--   **Formalization Note** The standing hypotheses of the contact process (Harris, §2(b), p. 971; §3, p. 972) are written as binders: $d \ge 1$, $\mu \ge 0$, $\lambda_0 = 0$ and $\lambda_k \ge 0$ for $0 \le k \le 2d$. Rates $\lambda_k$ with $k > 2d$ never enter the model, and no hypothesis mentions them. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$. $\Lambda$ is the maximum of $\lambda_0,\dots,\lambda_{2d}$ (a finite maximum, nonnegative since $\lambda_0=0$). The paper's proof goes through the Markov property of the infinite-volume process; the statement is unchanged.
-- source:
--   Harris (Ann. Probab. 2, 1974), Lemma 4.7, p. 975

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Lemma 4.7, p. 975: for a contact process started from a finite
set `ξ`, `m_t(ξ) ≤ |ξ| e^{(2dΛ − μ)t}` for `t ≥ 0`, where `Λ = max_{0 ≤ i ≤ 2d} λ_i`. -/
theorem lemma_4_7 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (t : ℝ) (ht : 0 ≤ t) (ξ : HarrisContact.Extinction.Config d) :
    HarrisContact.Extinction.meanSize μ lam t ξ ≤ (ξ.card : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp ((2 * (d : ℝ) * (Finset.range (2 * d + 1)).sup' (by simp) lam - μ) * t)) := by sorry
end HarrisContact.MeanSize
