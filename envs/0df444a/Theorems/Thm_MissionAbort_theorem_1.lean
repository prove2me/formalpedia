-- Prove2me | Theorems.Thm_MissionAbort_theorem_1
-- name    : MissionAbort.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:54:58.639005+00:00
-- url     : https://prove2.me/theorems/fd40a22f-f0c2-4a8e-a6be-49185e068a45
-- title:
--   Theorem 1: Erlang-surrogate policies converge almost surely to the optimal abort rules
-- statement:
--   Let $F,G$ be lifetime laws, let $\zeta>0$, and let $m_1(\lambda),m_2(\lambda)$ be integer-valued with $m_1,m_2\ge 1$ and $m_i(\lambda)/\lambda\to\infty$. Let $(\Omega,\mathbb P,T,Y)$ be the original system, with failure process $X$, and for every $\lambda>\zeta$ let $(\Omega^{(\lambda)},P^{(\lambda)},X^{(\lambda)},Y^{(\lambda)})$ be the surrogate system (4)–(6). Let $a^*$ and $a^*_\lambda$ be admissible rule families that compare the two costs-to-go at every history of positive probability in $[K]^n$, under $\mathbb P$ and under $P^{(\lambda)}$ respectively, and suppose that $\mathbb C_{ab}(n,y)\ne\mathbb C_c(n,y)$ at every such history under $\mathbb P$.
--
--   Write $\mathfrak T^*$ and $\mathfrak T^{(\lambda)}$ for the stopping times of $a^*$ and $a^*_\lambda$ on the signals $Y$, and $\mathfrak T^{(\lambda*)}$ for the stopping time of $a^*_\lambda$ on $Y^{(\lambda)}$. Then:
--
--   1. $a^*$ solves Problem (1), and $a^*_\lambda$ solves Problem (7) for every $\lambda>\zeta$.
--   2. For every $n\in[N-1]$, $a^*_{\lambda,n}(Y_{1:n})\to a^*_n(Y_{1:n})$ $\mathbb P$-almost surely as $\lambda\to\infty$.
--   3. $C\big(X(\mathfrak T^{(\lambda)}+w_{\mathfrak T^{(\lambda)}/\delta}),\mathfrak T^{(\lambda)}\big)\to C\big(X(\mathfrak T^*+w_{\mathfrak T^*/\delta}),\mathfrak T^*\big)$ $\mathbb P$-almost surely as $\lambda\to\infty$.
--   4. The two equalities of (8) hold:
--   $$
--   \mathbb E\big[C(X(\mathfrak T^*+w_{\mathfrak T^*/\delta}),\mathfrak T^*)\big]=\lim_{\lambda\to\infty}\mathbb E\big[C(X(\mathfrak T^{(\lambda)}+w_{\mathfrak T^{(\lambda)}/\delta}),\mathfrak T^{(\lambda)})\big]=\lim_{\lambda\to\infty}\mathbb E^{(\lambda)}\big[C(X^{(\lambda)}(\mathfrak T^{(\lambda*)}+w_{\mathfrak T^{(\lambda*)}/\delta}),\mathfrak T^{(\lambda*)})\big].
--   $$
--
--   The first equality of (8) says that the surrogate's rules are asymptotically optimal when applied in the original non-Markovian system, which is the guarantee behind the surrogate method. Clause 1 ties the rules to the two problems.
--
--   Differences from the source:
--   - reading: "We assume the set of optimal actions is unique" (p.11) → $\mathbb C_{ab}(n,y)\ne\mathbb C_c(n,y)$ at every $n\in[N-1]$ and every positive-probability history $y\in[K]^n$; reason: read as "the minimizer of (1) is a singleton" it is unsatisfiable for $N\ge 3$; this is how the proof uses it (pp.EC.3–EC.4)
--   - reading: $a^*$, $a^*_\lambda$ the optimal actions of (1), (7) → admissible rules that compare the costs-to-go at positive-probability histories, with clause 1 stating that they solve (1), (7); reason: a bare minimizer says nothing at histories after an earlier abort, so the almost-sure clause needs this; it is the proof's first paragraph (p.EC.2)
--   - reading: signals related to the state by $d_{ik}$ (p.10) → signals conditionally independent given the failure process; reason: the page is silent; the proof uses it (p.EC.2)
--   - reading: "$n\in[N]$" in the definition of $\mathfrak T$ in (7) → $n\in[N-1]$; reason: a slip: there is no rule $a_{\lambda,N}$, and the same display indexes the rules by $[N-1]$
--   - generalization: ties of the surrogate broken toward the smallest $\mathfrak T^{(\lambda*)}$ (p.15), or strictly (p.EC.2) → any tie-break of the surrogate; reason: both conventions are included
--   - generalization: $T_{12},T_{23}$ with densities → $F,G$ with no atoms, carried by $[0,\infty)$; reason: the proof uses only continuity of the CDFs; laws with densities satisfy this
--   - generalization: $X^{(\lambda)}$ a continuous-time Markov chain → $X^{(\lambda)}$ has the law of the chain on the finite decision grid; reason: a genuine chain satisfies this
--   - generalization: $w_n$ nondecreasing, Assumption 3(i) (p.10) → $w_n\ge 0$, not monotone; reason: the proof does not use monotonicity; nondecreasing $w_n$ are included
--   - encoding: $\mathfrak T/\delta$; (6) at $0/0$ → a stopping index $n$; the value $0$ of $x/0$; reason: the index is the same object; the states where (6) is $0/0$ are reached with probability zero
--   - encoding: the rate $\lambda$, states $\{1,\dots,m_1+m_2+1\}$, rules with values $\{0,1\}$, costs → `lam : ℝ`, 0-based states, `Bool`-valued rules, $C_m,C_s\ge 0$; reason: Lean reserves `λ`; the Lean state $x$ is the page's $x+1$; the page calls $C_m,C_s$ costs; same instances
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Theorem 1, p.15; proof Appendix A.2, pp.EC.2–EC.4

import Mathlib
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_IsLifetimeLaw
import Definitions.Def_MissionAbort_IsOriginalSystem
import Definitions.Def_MissionAbort_stateProcess
import Definitions.Def_MissionAbort_clusterProcess
import Definitions.Def_MissionAbort_IsSurrogateSystem
import Definitions.Def_MissionAbort_Rule
import Definitions.Def_MissionAbort_IsAdmissible
import Definitions.Def_MissionAbort_cost
import Definitions.Def_MissionAbort_realizedCost
import Definitions.Def_MissionAbort_expectedCost
import Definitions.Def_MissionAbort_IsMinimizer
import Definitions.Def_MissionAbort_hist
import Definitions.Def_MissionAbort_IsSeqOptimal
import Definitions.Def_MissionAbort_NoTies

open MeasureTheory ProbabilityTheory Filter Topology

namespace MissionAbort

/-- **Theorem 1** (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1, p.15; proof Appendix A.2, pp.EC.2–EC.4).
Let `(Ω, P, T, Y)` be the original system with laws `F`, `G`, and for every `λ > ζ` let
`(Ω⁽λ⁾, P⁽λ⁾, X⁽λ⁾, Y⁽λ⁾)` be the surrogate system (4)–(6) with `m₁(λ)/λ → ∞`, `m₂(λ)/λ → ∞`. Let `aStar`
and `a λ` be admissible rules that compare the two costs-to-go at positive-probability histories in
`[K]ⁿ`, under `P` and under `P⁽λ⁾` respectively, and suppose there is no tie under `P`. Then these rules
solve Problem (1) and Problem (7) respectively; for every `n ∈ [N − 1]`,
`a∗_{λ,n}(Y_{1:n}) → a∗ₙ(Y_{1:n})` `P`-almost surely; the realized cost converges `P`-almost surely;
and both equalities of (8) hold: `E[C(a∗)] = lim E[C(a⁽λ⁾)] = lim E⁽λ⁾[C(a⁽λ⁾)]`.

**Formalization Note.** `NoTies` is the reading of "the set of optimal actions is unique" (p.11) that
the proof uses (pp.EC.3–EC.4). Rules are pinned by `IsSeqOptimal` at every positive-probability history,
including those after an earlier abort, because the clause for `n` concerns all of them and a bare
minimizer of (1) says nothing there. Assumptions 1, 2, 3 of the paper are not hypotheses of Theorem 1.
`lam` is the page's `λ`; Lean reserves `λ`. Convergence of `Bool` values is eventual equality. -/
theorem theorem_1 {K : ℕ} (M : Model K) (F G : Measure ℝ) (hF : IsLifetimeLaw F) (hG : IsLifetimeLaw G)
    (m₁ m₂ : ℝ → ℕ) (hm₁ : Tendsto (fun lam => (m₁ lam : ℝ) / lam) atTop atTop)
    (hm₂ : Tendsto (fun lam => (m₂ lam : ℝ) / lam) atTop atTop)
    (hm₁_pos : ∀ lam, M.ζ < lam → 0 < m₁ lam) (hm₂_pos : ∀ lam, M.ζ < lam → 0 < m₂ lam)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Ω → ℝ × ℝ × ℝ) (Y : ℕ → Ω → Fin (K + 1))
    (horig : IsOriginalSystem M F G P T Y)
    {Ωs : ℝ → Type*} [∀ lam, MeasurableSpace (Ωs lam)] (Ps : ∀ lam, Measure (Ωs lam))
    (X : ∀ lam, ℝ → Ωs lam → Fin (m₁ lam + m₂ lam + 1)) (Ys : ∀ lam, ℕ → Ωs lam → Fin (K + 1))
    (hsur : ∀ lam, M.ζ < lam →
      IsSurrogateSystem M F G lam (m₁ lam) (m₂ lam) (Ps lam) (X lam) (Ys lam))
    (aStar : Rule K) (a : ℝ → Rule K)
    (haStar : IsAdmissible M.N aStar) (hoptStar : IsSeqOptimal M P (stateProcess T) Y aStar)
    (ha : ∀ lam, M.ζ < lam → IsAdmissible M.N (a lam))
    (hopt : ∀ lam, M.ζ < lam →
      IsSeqOptimal M (Ps lam) (clusterProcess (X lam)) (Ys lam) (a lam))
    (hunique : NoTies M P (stateProcess T) Y) :
    IsMinimizer M P (stateProcess T) Y aStar ∧
    (∀ lam, M.ζ < lam → IsMinimizer M (Ps lam) (clusterProcess (X lam)) (Ys lam) (a lam)) ∧
    (∀ n, 1 ≤ n → n < M.N → ∀ᵐ ω ∂P,
      Tendsto (fun lam => a lam n (hist Y n ω)) atTop (𝓝 (aStar n (hist Y n ω)))) ∧
    (∀ᵐ ω ∂P,
      Tendsto (fun lam => realizedCost M (stateProcess T) Y (a lam) ω) atTop
        (𝓝 (realizedCost M (stateProcess T) Y aStar ω))) ∧
    Tendsto (fun lam => expectedCost M P (stateProcess T) Y (a lam)) atTop
      (𝓝 (expectedCost M P (stateProcess T) Y aStar)) ∧
    Tendsto (fun lam => expectedCost M (Ps lam) (clusterProcess (X lam)) (Ys lam) (a lam)) atTop
      (𝓝 (expectedCost M P (stateProcess T) Y aStar)) := by sorry

end MissionAbort
