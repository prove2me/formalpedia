-- Prove2me | Theorems.Thm_MissionAbort_proposition_1
-- name    : MissionAbort.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:52:22.1057+00:00
-- url     : https://prove2.me/theorems/44d971db-8324-4deb-9e45-7806dcf93992
-- title:
--   Proposition 1 (corrected: the first hitting time of $\mathcal X_2$ is $T_{12}^{(\lambda)}$ only on $\{T_{12}^{(\lambda)}<T_{13}\}$, stated as the law of the cluster process)
-- statement:
--   Let $F,G$ be laws as in the mission, $0<\zeta<\lambda$ and $m_1,m_2\ge 1$. Let $Q$ be the rate matrix (5), (6) and $\pi_0^{(\lambda)}$ the initial distribution (4). Let $G^{(\lambda)}$, $F^{(\lambda)}$ be the Erlang mixtures (3), (2), and let $T_{12}^{(\lambda)}\sim G^{(\lambda)}$, $T_{13}\sim\mathrm{Exp}(\zeta)$ and $T_{23}^{(\lambda)}\sim F^{(\lambda)}$ be independent.
--
--   For all times $0=t_0\le t_1\le\dots\le t_k$ and clusters $c_0,\dots,c_k$,
--   $$
--   \sum_{\substack{s_0,\dots,s_k\\ s_j\in c_j}}\pi_0^{(\lambda)}(s_0)\prod_{i=0}^{k-1}\big[e^{(t_{i+1}-t_i)Q}\big]_{s_is_{i+1}}=\mathbb P\Big(\mathrm{state}\big(T_{12}^{(\lambda)},T_{13},T_{23}^{(\lambda)};t_j\big)=c_j\ \ \forall j\Big).
--   $$
--
--   So the cluster process of the surrogate chain has the law of the state function of the independent triple. Taking $k=1$, $c_1=$ failed and summing over $c_0$ gives the absorption clause of the proposition: the absorption time has the law of $T_{13}\mathbb 1\{T_{13}\le T_{12}^{(\lambda)}\}+(T_{12}^{(\lambda)}+T_{23}^{(\lambda)})\mathbb 1\{T_{13}>T_{12}^{(\lambda)}\}$. This identity is what links the surrogate problem to the Erlang mixtures, and the proof of Theorem 1 relies on all of it.
--
--   Differences from the source:
--   - correction: the first hitting time of $X^{(\lambda)}$ to $\mathcal X_2$ has the same distribution as $T_{12}^{(\lambda)}$ → the joint law of the cluster process at finitely many times equals that of the state function of the independent triple; reason: false as printed: at $\zeta=1,\lambda=5,m_1=m_2=4,G=\mathrm{Exp}(3/2),F=\mathrm{Exp}(2)$ the chain ever reaches $\mathcal X_2$ with probability $0.5963<1$ (it may be absorbed from $\mathcal X_1$), while $T_{12}^{(\lambda)}$ is finite almost surely; the true hitting time has the law of $T_{12}^{(\lambda)}$ on $\{T_{12}^{(\lambda)}<T_{13}\}$ and is $+\infty$ elsewhere
--   - generalization: $F,G$ with densities → $F,G$ with no atoms; reason: the proof uses only $F(0)=G(0)=0$; laws with densities satisfy this
--   - encoding: a statement about the process $X^{(\lambda)}$ → a matrix identity with the transition function $e^{tQ}$; reason: this is the finite-dimensional law of the chain; same instances
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Proposition 1, p.14; proof Appendix A.1, pp.EC.1–EC.2

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_state
import Definitions.Def_MissionAbort_timeLaw
import Definitions.Def_MissionAbort_IsLifetimeLaw
import Definitions.Def_MissionAbort_erlangMix
import Definitions.Def_MissionAbort_pathWeight
import Definitions.Def_MissionAbort_clusterOf
import Definitions.Def_MissionAbort_initialProb
import Definitions.Def_MissionAbort_rateMatrix

open MeasureTheory ProbabilityTheory Filter Topology

namespace MissionAbort

/-- **Proposition 1 (corrected)** (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1, p.14; proof Appendix A.1,
pp.EC.1–EC.2). For the rate matrix (5), (6) and the initial law (4), the cluster process of the
surrogate chain has the finite-dimensional laws of the state function of independent
`(T₁₂⁽λ⁾, T₁₃, T₂₃⁽λ⁾)` with laws `G⁽λ⁾` of (3), exponential of rate `ζ`, and `F⁽λ⁾` of (2): summing
the chain's path weights over the paths in the clusters `c₀, …, c_k` at times `0 = t₀ ≤ ⋯ ≤ t_k`
gives the probability that the state function visits those clusters at those times.

**Formalization Note.** The printed first clause, that the first hitting time of `X₂` has the law of
`T₁₂⁽λ⁾`, is false: the chain may be absorbed from `X₁` and never reach `X₂`, and the page's own
proof speaks of "potential" transition times. The printed absorption clause is the case
`k = 1`, `t₀ = 0`, with `c₁ = failed` summed over `c₀`. The identity carries no process. -/
theorem proposition_1 (F G : Measure ℝ) (hF : IsLifetimeLaw F) (hG : IsLifetimeLaw G)
    (ζ lam : ℝ) (hζ : 0 < ζ) (hlam : ζ < lam) (m₁ m₂ : ℕ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (k : ℕ) (t : Fin (k + 1) → ℝ) (ht0 : t 0 = 0) (ht : Monotone t) (c : Fin (k + 1) → Cluster) :
    ∑ s ∈ Finset.univ.filter
        (fun s : Fin (k + 1) → Fin (m₁ + m₂ + 1) => ∀ j, clusterOf m₁ m₂ (s j) = c j),
      pathWeight (initialProb G ζ lam m₁ m₂) (rateMatrix F ζ lam m₁ m₂) t s =
    (timeLaw (erlangMix G m₁ (lam - ζ)) ζ (erlangMix F m₂ lam)).real
      {u | ∀ j, state u (t j) = c j} := by sorry

end MissionAbort
