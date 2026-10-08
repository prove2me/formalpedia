-- Prove2me | Theorems.Thm_HighDimProb_Chaining_dudley_integral_inequality_v2
-- name    : HighDimProb.Chaining.dudley_integral_inequality_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:41.321619+00:00
-- url     : https://prove2.me/theorems/bcf6828d-cf28-43de-b33d-6eb94630ecde
-- title:
--   Theorem 8.1.3 — Dudley's integral inequality: $\mathbb E\sup_{t\in T}X_t \le CK\int_0^\infty\sqrt{\log N(T,d,\varepsilon)}\,d\varepsilon$
-- statement:
--   This is **Dudley's integral inequality**, the chapter's main theorem: a bound on the expected supremum of a general (not necessarily Gaussian) random process with sub-gaussian increments in terms of the metric entropy of its index set, obtained by chaining, the multi-scale refinement of the $\varepsilon$-net argument.
--
--   There is an absolute constant $C>0$ such that the following holds. Let $(X_t)_{t\in T}$ be a mean-zero random process on a (nonempty) metric space $(T,d)$ with **sub-gaussian increments** (Definition 8.1.1, Eq. (8.1)): there is $K\ge0$ such that
--   $$
--   \|X_t-X_s\|_{\psi_2}\;\le\;K\,d(t,s)\qquad\text{for all }t,s\in T,
--   $$
--   where $\|\cdot\|_{\psi_2}$ is the sub-gaussian norm (companion definition `HighDimProb.Concentration.subgaussianNorm`, valued in $[0,\infty]$, finite exactly for sub-gaussian variables). Then
--   $$
--   \mathbb E\sup_{t\in T}X_t\;\le\;CK\int_0^\infty\sqrt{\log N(T,d,\varepsilon)}\;d\varepsilon,
--   $$
--   where $N(T,d,\varepsilon)\in\mathbb N\cup\{\infty\}$ is the covering number (`coveringNumber`), the integral is a Lebesgue integral in $[0,\infty]$ whose integrand is $+\infty$ wherever $N(T,d,\varepsilon)=\infty$, and $\mathbb E\sup_{t\in T}X_t:=\sup\{\mathbb E\max_{t\in T_0}X_t : T_0\subseteq T\text{ finite nonempty}\}$ (`processESup`), the book's own convention (footnote 3 to §7.2) for the expected supremum of a process over an arbitrary index set.
--
--   **Formalization Note.** The retired version was disproved because its real-valued sub-gaussian norm returned the junk value $0$ for a non-sub-gaussian increment, so a process with an integrable but not sub-gaussian increment satisfied (8.1) with $K=0$ while $\mathbb E\sup X_t>0$. The new statement differs in three ways. (i) The increment hypothesis uses the corrected `ℝ≥0∞`-valued norm and $K\in[0,\infty)$ (`ℝ≥0`), written $\|X_t-X_s\|_{\psi_2}\le K\cdot d(t,s)$ in $[0,\infty]$, so it now says that every increment *is* sub-gaussian with the stated bound. (ii) The metric-entropy integral is `lintegral` over $(0,\infty)$ of the $[0,\infty]$-valued integrand "$\sqrt{\log N(T,d,\varepsilon)}$ if $N(T,d,\varepsilon)<\infty$, $+\infty$ otherwise", so it is $+\infty$ exactly when the book's integral is (a non-totally-bounded $T$, or an integrand not integrable at $0$), in which case the book's bound is trivially true; the retired version's extra hypotheses that $T$ be totally bounded and that the integrand be integrable on $(0,\infty)$ — which excluded those trivially true cases — are dropped, so no hypothesis beyond the book's remains. (iii) The right-hand side $CK\int\cdots$ is computed in $[0,\infty]$ and compared with the `EReal`-valued $\mathbb E\sup$; with $K=0$ all increments vanish a.s. and both sides are $0$, so the convention $0\cdot\infty=0$ is harmless. Conventions made explicit: mean zero is "$X_t$ integrable and $\mathbb E X_t=0$"; $T$ is nonempty (a process has a nonempty index set; every $\varepsilon$-net is then nonempty, so $N\ge1$ and $\log N\ge0$); $C$ is existentially quantified before every other object; no separability or measurability of the supremum is assumed because the book's finite-marginal definition of $\mathbb E\sup$ needs none, and the book's reduction "we may assume $T$ is finite" is exactly this convention (for finite $T_0\subseteq T$, $N(T_0,d,\varepsilon)\le N(T,d,\varepsilon/2)$, the factor $2$ being absorbed into $C$).
-- source:
--   Vershynin, High-Dimensional Probability (CUP 2018), Theorem 8.1.3 with Definition 8.1.1 / Eq. (8.1), p. 188 (PDF p. 196); E sup convention: footnote 3 to §7.2, p. 160; sub-gaussian norm Definition 2.5.6, p. 28

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
import Definitions.Def_HighDimProb_Chaining_CoveringNumber
import Definitions.Def_HighDimProb_Chaining_ProcessESup

open MeasureTheory
open scoped ENNReal NNReal

namespace HighDimProb.Chaining

/-- **Theorem 8.1.3** (Dudley's integral inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 188 (PDF p. 196).

"Let `(X_t)_{t∈T}` be a mean zero random process on a metric space `(T,d)` with sub-gaussian
increments as in (8.1) [`‖X_t − X_s‖_{ψ2} ≤ K d(t,s)` for all `t,s ∈ T`, some `K ≥ 0`]. Then
`E sup_{t∈T} X_t ≤ CK ∫_0^∞ √(log N(T,d,ε)) dε`."

`E sup` is `processESup` (`EReal`-valued, through finite marginals, the book's own convention of
footnote 3 to Section 7.2, which is why no separability of the process is needed); `N(T,d,·)` is
`coveringNumber` (`ℕ∞`-valued, `⊤` when `T` has no finite `ε`-net). Mean zero is
`Integrable (X t) P ∧ ∫ X t = 0`. `[Nonempty T]` is the standing convention that a process has
a nonempty index set (it makes every `ε`-net nonempty, so `N(T,d,ε) ≥ 1` and `log` is only
evaluated on `[1, ∞)`).

Corrected version (`_v2`). (i) The sub-gaussian norm is the corrected `ℝ≥0∞`-valued
`HighDimProb.Concentration.subgaussianNorm` (`⊤` for a non-sub-gaussian increment) and
`K : ℝ≥0`, so (8.1) now says the increments *are* sub-gaussian with `‖X_t − X_s‖_{ψ₂} ≤ K d(t,s)`;
the retired version's real-valued norm returned `0` for a non-sub-gaussian increment, so the
hypothesis held with `K = 0`. (ii) The metric-entropy integral `∫_0^∞ √(log N(T,d,ε)) dε` is a
Lebesgue integral in `ℝ≥0∞` (`lintegral` over `Set.Ioi 0`) of the integrand that is
`√(log N(T,d,ε))` when `N(T,d,ε)` is finite and `⊤` when it is infinite, so the integral is
`+∞` exactly when the book's is (non-totally-bounded `T`, or an integrand diverging at `0`), in
which case the book's bound is trivially true — the retired version's extra hypotheses that `T`
be totally bounded and the integrand be integrable on `(0,∞)` are dropped. (iii) The right-hand
side `C K ∫…` is computed in `ℝ≥0∞` (`ENNReal.ofReal C * K * ∫⁻ …`) and coerced to `EReal`. -/
theorem dudley_integral_inequality_v2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {T : Type} [MetricSpace T] [Nonempty T] (X : T → Ω → ℝ) (K : ℝ≥0),
        (∀ t, Integrable (X t) P ∧ ∫ ω, X t ω ∂P = 0) →
        (∀ t s, HighDimProb.Concentration.subgaussianNorm P (fun ω => X t ω - X s ω) ≤
          (K : ℝ≥0∞) * ENNReal.ofReal (dist t s)) →
        processESup P X ≤
          ((ENNReal.ofReal C * (K : ℝ≥0∞) *
              ∫⁻ ε in Set.Ioi (0 : ℝ),
                (if coveringNumber T ε = ⊤ then (⊤ : ℝ≥0∞)
                 else ENNReal.ofReal
                   (Real.sqrt (Real.log ((coveringNumber T ε).toNat : ℝ)))) : ℝ≥0∞) : EReal) := by
  sorry

end HighDimProb.Chaining
