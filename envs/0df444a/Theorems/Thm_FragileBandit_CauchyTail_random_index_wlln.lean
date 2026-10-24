-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_random_index_wlln
-- name    : FragileBandit.CauchyTail.random_index_wlln
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:47.623287+00:00
-- url     : https://prove2.me/theorems/768eb440-44ec-4471-88f7-7444502759e7
-- title:
--   (15), p. 14 — random-index weak law of large numbers for the rewards of one arm
-- statement:
--   **Weak law of large numbers along a random number of plays.** Let $\nu = (Q_1,\dots,Q_K)$ be any environment, $\pi$ any algorithm and $j$ an arm whose number of plays tends to infinity in probability:
--
--   $$\lim_{T\to\infty}\mathbb P_{\nu\pi}\big(N_j(T) \le m\big) = 0 \quad \text{for every } m \in \mathbb N.$$
--
--   Let $\varphi : \mathbb R \to \mathbb R$ be measurable and $Q_j$-integrable, and let $X_j(1), X_j(2), \dots$ be the successive rewards of arm $j$. Then for every $\delta > 0$,
--
--   $$\lim_{T\to\infty}\mathbb P_{\nu\pi}\Big(\Big|\frac{1}{N_j(T)}\sum_{s=1}^{N_j(T)}\varphi\big(X_j(s)\big) - \int \varphi\,dQ_j\Big| > \delta\Big) = 0.$$
--
--   In the paper this is the step "by (14) and the WLLN" giving (15), with $\varphi = \log dP^{\mu_1}/dP^{\tilde\mu_1}$ and $\int\varphi\,dP^{\tilde\mu_1} = -d_P(\tilde\mu_1,\mu_1)$; the same step gives $\lim\mathbb P_{\tilde\nu\pi}(\mathcal B_T) = 1$ on p. 38 and $\lim \mathbb P_{\tilde\nu\pi}(\mathcal B_n) = 1$ on p. 46. The difficulty is that the policy is adaptive, so the number of terms is a random time depending on the rewards themselves.
--
--   **Formalization Note** The sample average is the sum of $\varphi$ over the rounds $t \le T$ in which arm $j$ was played, divided by $N_j(T)$; when $N_j(T) = 0$ Lean's division gives $0$, an event whose probability vanishes under the hypothesis.
--
--   Differences from the source:
--   - generalization: (15): φ = log dP^{µ1}/dP^{µ̃1} under ν̃, with N_1(T)/log T → 1/d_P(µ̃1, µ2) in probability (14) → any environment, algorithm and arm j with N_j(T) → ∞ in probability, and any measurable Q_j-integrable φ; reason: (14) implies N_1(T) → ∞ in probability, and φ = log dP^{µ1}/dP^{µ̃1} is measurable and P^{µ̃1}-integrable with integral −d_P(µ̃1, µ1), so (15) is the special case
--   - encoding: (1/N_j(T)) Σ_{s=1}^{N_j(T)} φ(X_j(s)) → (Σ over rounds t ≤ T with A(t) = j of φ(Y(t))) / N_j(T), with value 0 when N_j(T) = 0; reason: the rewards of the rounds in which j is played are X_j(1), …, X_j(N_j(T)); the N_j(T) = 0 event has vanishing probability
--   - encoding: P_νπ on ([K] × ℝ)^∞ (p. 7), events about N_i(T) → banditMeasure ν π T on the histories of the first T rounds (published BanditPolicy), N_i(T) = armPullCount i h; reason: the infinite-horizon law restricted to the first T rounds is exactly banditMeasure ν π T, and N_i(T) depends only on those rounds
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p. 14, (14)–(15) ('by (14) and the WLLN'); p. 38 and p. 46 ('the WLLN for sample means')

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- Random-index weak law of large numbers ((15), p. 14; "the WLLN for sample means", pp. 38 and 46):
if the number of plays `N_j(T)` of arm `j` tends to infinity in `P_νπ`-probability, then for every
`Q_j`-integrable `φ` the average of `φ` over the rewards of arm `j` up to time `T`,
`(1/N_j(T)) ∑_{s ≤ N_j(T)} φ(X_j(s))`, converges in `P_νπ`-probability to `∫ φ dQ_j`. -/
theorem random_index_wlln {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (j : Fin K)
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφ : Integrable φ (ν.P j))
    (hN : ∀ m : ℕ, Tendsto (fun T : ℕ => banditMeasure ν π T {h | armPullCount j h ≤ m})
      atTop (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => banditMeasure ν π T
      {h | δ < |(∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ (h t).2) /
          (armPullCount j h : ℝ) - ∫ y, φ y ∂(ν.P j)|}) atTop (𝓝 0) := by sorry

end FragileBandit.CauchyTail
