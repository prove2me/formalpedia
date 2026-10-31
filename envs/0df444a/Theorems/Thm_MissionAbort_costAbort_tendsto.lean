-- Prove2me | Theorems.Thm_MissionAbort_costAbort_tendsto
-- name    : MissionAbort.costAbort_tendsto
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:20.232169+00:00
-- url     : https://prove2.me/theorems/25df1bf7-a0d5-4699-981b-a832bf441ece
-- title:
--   Appendix A.2: the abort cost-to-go converges
-- statement:
--   Let $(\Omega,\mathbb P,T,Y)$ be the original system with lifetime laws $F,G$, and for every $\lambda>\zeta$ let $(\Omega^{(\lambda)},P^{(\lambda)},X^{(\lambda)},Y^{(\lambda)})$ be the surrogate system with $m_1(\lambda),m_2(\lambda)\ge 1$ and $m_i(\lambda)/\lambda\to\infty$.
--
--   Let $n\le N$ and let $y$ be a history with $\mathbb P(Y_{1:n}=y)>0$. Then
--   $$
--   P^{(\lambda)}\big(Y^{(\lambda)}_{1:n}=y\big)\longrightarrow\mathbb P(Y_{1:n}=y)\quad\text{and}\quad\mathbb C_{ab,\lambda}(n,y)\longrightarrow\mathbb C_{ab}(n,y)\qquad(\lambda\to\infty).
--   $$
--
--   The first limit shows that the history is eventually of positive probability under the surrogate, which is what makes the conditional probabilities in $\mathbb C_{ab,\lambda}$ meaningful. Here $\mathbb C_{ab,\lambda}$ is computed for the cluster process of $X^{(\lambda)}$ under $P^{(\lambda)}$.
--
--   Differences from the source:
--   - reading: the limit for all $y_{1:n}$ → the limit at histories of positive probability under the original law; reason: conditional probabilities at null histories are undefined on the page
--   - generalization: $F,G$ with densities; a chain $X^{(\lambda)}$ → $F,G$ with no atoms; the law of $X^{(\lambda)}$ on the decision grid; reason: the proof uses nothing more; a genuine chain with such laws satisfies this
--   - encoding: $\{\xi\le t\}$ → $\{S(t)=\text{failed}\}$; reason: the same event, the failed state being absorbing; the clause on history probabilities is the denominator of the page's display
--   - generalization: $n\in[N]$ → $0\le n\le N$; reason: adds $n=0$, where $\mathbb C_{ab}(0,\langle\rangle)=C_m$ under both laws; every $n\in[N]$ is included
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, p.EC.3

import Mathlib
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_IsLifetimeLaw
import Definitions.Def_MissionAbort_IsOriginalSystem
import Definitions.Def_MissionAbort_stateProcess
import Definitions.Def_MissionAbort_clusterProcess
import Definitions.Def_MissionAbort_IsSurrogateSystem
import Definitions.Def_MissionAbort_cost
import Definitions.Def_MissionAbort_histEvent
import Definitions.Def_MissionAbort_costAbort

open MeasureTheory ProbabilityTheory Filter Topology

namespace MissionAbort

/-- **The abort cost-to-go converges** (Sun, Hu & Ye, arXiv:2505.03225v1, Appendix A.2, p.EC.3,
"`lim Cab,λ(n, y1:n) = Cab(n, y1:n)`"). At a history `y` of positive probability under the original
law, the surrogate history probabilities converge to the original one, so they are eventually positive,
and `Cab,λ(n, y) → Cab(n, y)`.

**Formalization Note.** The surrogate quantities are computed under `P⁽λ⁾` for the cluster process
of `X⁽λ⁾`. Nothing is asserted at a history that is null under the original law. -/
theorem costAbort_tendsto {K : ℕ} (M : Model K) (F G : Measure ℝ) (hF : IsLifetimeLaw F) (hG : IsLifetimeLaw G)
    (m₁ m₂ : ℝ → ℕ) (hm₁ : Tendsto (fun lam => (m₁ lam : ℝ) / lam) atTop atTop)
    (hm₂ : Tendsto (fun lam => (m₂ lam : ℝ) / lam) atTop atTop)
    (hm₁_pos : ∀ lam, M.ζ < lam → 0 < m₁ lam) (hm₂_pos : ∀ lam, M.ζ < lam → 0 < m₂ lam)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Ω → ℝ × ℝ × ℝ) (Y : ℕ → Ω → Fin (K + 1))
    (horig : IsOriginalSystem M F G P T Y)
    {Ωs : ℝ → Type*} [∀ lam, MeasurableSpace (Ωs lam)] (Ps : ∀ lam, Measure (Ωs lam))
    (X : ∀ lam, ℝ → Ωs lam → Fin (m₁ lam + m₂ lam + 1)) (Ys : ∀ lam, ℕ → Ωs lam → Fin (K + 1))
    (hsur : ∀ lam, M.ζ < lam →
      IsSurrogateSystem M F G lam (m₁ lam) (m₂ lam) (Ps lam) (X lam) (Ys lam))
    (n : ℕ) (hn : n ≤ M.N) (y : Fin n → Fin (K + 1)) (hy : 0 < P.real (histEvent Y n y)) :
    Tendsto (fun lam => (Ps lam).real (histEvent (Ys lam) n y)) atTop
      (𝓝 (P.real (histEvent Y n y))) ∧
    Tendsto (fun lam => costAbort M (Ps lam) (clusterProcess (X lam)) (Ys lam) n y) atTop
      (𝓝 (costAbort M P (stateProcess T) Y n y)) := by sorry

end MissionAbort
