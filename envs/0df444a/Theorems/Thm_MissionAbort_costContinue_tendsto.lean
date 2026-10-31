-- Prove2me | Theorems.Thm_MissionAbort_costContinue_tendsto
-- name    : MissionAbort.costContinue_tendsto
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:58.137969+00:00
-- url     : https://prove2.me/theorems/b838bd34-bec3-420d-b4e1-8aba03f15557
-- title:
--   Appendix A.2: the continue cost-to-go converges
-- statement:
--   Let $(\Omega,\mathbb P,T,Y)$ be the original system with lifetime laws $F,G$, and for every $\lambda>\zeta$ let $(\Omega^{(\lambda)},P^{(\lambda)},X^{(\lambda)},Y^{(\lambda)})$ be the surrogate system with $m_1(\lambda),m_2(\lambda)\ge 1$ and $m_i(\lambda)/\lambda\to\infty$.
--
--   Let $n\le N-1$ and let $y$ be a history with $\mathbb P(Y_{1:n}=y)>0$. Then
--   $$
--   \mathbb C_{c,\lambda}(n,y)\longrightarrow\mathbb C_c(n,y)\qquad(\lambda\to\infty).
--   $$
--
--   At $n=0$ this says that the optimal value of the surrogate problem converges to the optimal value of the original problem. Because the recursion takes a minimum of the two costs-to-go, the argument does not need the rules to converge.
--
--   Differences from the source:
--   - generalization: the induction carries $a^*$ and the uniqueness assumption → no uniqueness hypothesis; reason: $\mathbb C_c$ recurses through $\min$, which is continuous; the printed case is included
--   - generalization: $F,G$ with densities; a chain $X^{(\lambda)}$ → $F,G$ with no atoms; the law of $X^{(\lambda)}$ on the decision grid; reason: the proof uses nothing more; a genuine chain with such laws satisfies this
--   - reading: the limit for all $y_{1:n}$ → the limit at histories of positive probability under the original law; reason: conditional probabilities at null histories are undefined on the page
--   - reading: $n\in[N]$ → $0\le n\le N-1$; reason: there is no continuation at $n=N$ (the mission ends at $H=N\delta$) and the page defines no $\mathbb C_c(N,\cdot)$; its induction closes with "true for all $n\in[N-1]$" (p.EC.4); $n=0$, the optimal value, is added
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, pp.EC.3–EC.4

import Mathlib
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_IsLifetimeLaw
import Definitions.Def_MissionAbort_IsOriginalSystem
import Definitions.Def_MissionAbort_stateProcess
import Definitions.Def_MissionAbort_clusterProcess
import Definitions.Def_MissionAbort_IsSurrogateSystem
import Definitions.Def_MissionAbort_cost
import Definitions.Def_MissionAbort_histEvent
import Definitions.Def_MissionAbort_costContinue
import Definitions.Def_MissionAbort_NoTies

open MeasureTheory ProbabilityTheory Filter Topology

namespace MissionAbort

/-- **The continue cost-to-go converges** (Sun, Hu & Ye, arXiv:2505.03225v1, Appendix A.2,
pp.EC.3–EC.4). At a history `y` of positive probability under the original law, for
`n = 0, …, N − 1`, `Cc,λ(n, y) → Cc(n, y)`. At `n = 0` this is the convergence of the optimal
values.

**Formalization Note.** The page carries the rule `a∗` and the uniqueness assumption through this
induction. The recursion through `min` needs neither, so `NoTies` is not a hypothesis here. -/
theorem costContinue_tendsto {K : ℕ} (M : Model K) (F G : Measure ℝ) (hF : IsLifetimeLaw F) (hG : IsLifetimeLaw G)
    (m₁ m₂ : ℝ → ℕ) (hm₁ : Tendsto (fun lam => (m₁ lam : ℝ) / lam) atTop atTop)
    (hm₂ : Tendsto (fun lam => (m₂ lam : ℝ) / lam) atTop atTop)
    (hm₁_pos : ∀ lam, M.ζ < lam → 0 < m₁ lam) (hm₂_pos : ∀ lam, M.ζ < lam → 0 < m₂ lam)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Ω → ℝ × ℝ × ℝ) (Y : ℕ → Ω → Fin (K + 1))
    (horig : IsOriginalSystem M F G P T Y)
    {Ωs : ℝ → Type*} [∀ lam, MeasurableSpace (Ωs lam)] (Ps : ∀ lam, Measure (Ωs lam))
    (X : ∀ lam, ℝ → Ωs lam → Fin (m₁ lam + m₂ lam + 1)) (Ys : ∀ lam, ℕ → Ωs lam → Fin (K + 1))
    (hsur : ∀ lam, M.ζ < lam →
      IsSurrogateSystem M F G lam (m₁ lam) (m₂ lam) (Ps lam) (X lam) (Ys lam))
    (n : ℕ) (hn : n < M.N) (y : Fin n → Fin (K + 1)) (hy : 0 < P.real (histEvent Y n y)) :
    Tendsto (fun lam => costContinue M (Ps lam) (clusterProcess (X lam)) (Ys lam) n y) atTop
      (𝓝 (costContinue M P (stateProcess T) Y n y)) := by sorry

end MissionAbort
