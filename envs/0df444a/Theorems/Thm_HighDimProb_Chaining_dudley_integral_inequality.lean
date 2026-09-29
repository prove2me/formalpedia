-- Prove2me | Theorems.Thm_HighDimProb_Chaining_dudley_integral_inequality
-- name    : HighDimProb.Chaining.dudley_integral_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:05:23.241471+00:00
-- url     : https://prove2.me/theorems/32e66e6f-bb7d-4094-8136-25578f7619a4
-- title:
--   Theorem 8.1.3 — Dudley's integral inequality
-- statement:
--   This is **Dudley's integral inequality**, the chapter's title result and its main theorem: a
--   bound on the expected supremum of a general (not necessarily Gaussian) random process with
--   sub-gaussian increments, in terms of the metric entropy of its index set, obtained by the
--   technique of **chaining** — a multi-scale refinement of the single-scale $\varepsilon$-net
--   argument.
--
--   Let $(X_t)_{t\in T}$ be a mean zero random process on a metric space $(T,d)$ with **sub-gaussian
--   increments**: there is $K \ge 0$ such that
--
--   $$
--   \lVert X_t - X_s \rVert_{\psi_2} \;\le\; K\, d(t,s) \qquad \text{for all } t,s\in T,
--   $$
--
--   where $\lVert\cdot\rVert_{\psi_2}$ is the sub-gaussian (Orlicz) norm (`SubgaussianNorm`, Def.
--   2.5.6, reused from Chapter 2). Then
--
--   $$
--   E \sup_{t\in T} X_t \;\le\; CK \int_0^\infty \sqrt{\log N(T,d,\varepsilon)}\; d\varepsilon,
--   $$
--
--   where $N(T,d,\varepsilon)$ is the covering number (`CoveringNumber`) and $C$ is an absolute
--   constant. The result generalizes Sudakov's minoration inequality's setting (Gaussian processes
--   with the canonical metric, Chapter 7) to arbitrary sub-gaussian processes, and generalizes
--   Sudakov's inequality's lower bound with a matching-up-to-a-log-factor upper bound.
--
--   **Formalization Note** $E\sup$ is `ProcessESup` (`EReal`-valued, through finite marginals).
--   Mean zero is stated as `Integrable (X t) P ∧ ∫ X t = 0` for every `t`, not the bare equation,
--   since a non-integrable variable's Bochner integral defaults to `0` regardless of its true
--   mean. For the right-hand integral over `Set.Ioi 0` to be a well-defined finite quantity — the
--   book's own statement treats it as one without spelling out why — two hypotheses make this
--   explicit rather than silently assumed: `T` totally bounded (`N(T,d,\varepsilon) < \infty` for
--   every $\varepsilon>0$) and the resulting integrand `IntegrableOn (Set.Ioi 0)`, which holds for
--   every totally bounded $(T,d)$ since the integrand vanishes once $\varepsilon \ge \mathrm{diam}\,
--   T$ (a single ball then covers $T$, so $N=1$ and $\log 1 = 0$). `[Nonempty T]` excludes the
--   degenerate empty index set, so $N(T,d,\varepsilon)\ge 1$ always and $\log$ is never evaluated
--   through an empty-$T$ edge case. `C` is existentially quantified before every type, instance,
--   and hypothesis it is uniform over, matching the book's "absolute constant."
--
--   This mission covers Theorem 8.1.3 and the combinatorial Sauer-Shelah Lemma (Theorem 8.3.16)
--   only, per `CAPTAIN_BRIEF.md`'s explicit scope-reduction allowance for this chapter: Theorem
--   8.3.18 (covering numbers via VC dimension) and Theorem 8.2.3 (the uniform law of large
--   numbers) are left out, not approximated, for lack of time to formalize the probability-space
--   machinery (measurability of the empirical process $X_f$, the class $F$ of Lipschitz
--   functions) they need beyond what this mission's other items already provide.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 188, Theorem 8.1.3

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm
import Definitions.Def_HighDimProb_Chaining_CoveringNumber
import Definitions.Def_HighDimProb_Chaining_ProcessESup

open MeasureTheory

namespace HighDimProb.Chaining

/-- **Theorem 8.1.3** (Dudley's integral inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 188 (PDF p. 196).

"Let `(X_t)_{t∈T}` be a mean zero random process on a metric space `(T,d)` with sub-gaussian
increments as in (8.1) [`‖X_t − X_s‖_{ψ2} ≤ K d(t,s)` for all `t,s ∈ T`]. Then `E sup_{t∈T} X_t ≤
CK ∫_0^∞ √(log N(T,d,ε)) dε`." The sub-gaussian norm is `HighDimProb.Concentration.subgaussianNorm`
(the published Definition 2.5.6/Eq. (2.13) `‖X‖_{ψ2}`, reused per `CAPTAIN_BRIEF.md` Addendum 2
rule 5). `E sup` is `processESup` and `N(T,d,·)` is `coveringNumber`, both redefined for this
chunk's own `MetricSpace T` convention. Mean zero is stated as `Integrable (X t) P ∧ ∫ X t = 0`
(not just the equation alone), since a non-integrable random variable's Bochner integral is `0` by
Mathlib convention regardless of its true mean, which would otherwise let a non-mean-zero process
through vacuously (trap 2, `reference/FAITHFULNESS_TRAPS.md`).

For the right-hand integral over `Set.Ioi 0` to be a well-defined finite real number — the pitfall
`BRIEF.md` flags explicitly — two extra hypotheses are added beyond the book's own displayed
statement, both implicit in speaking of "the" integral `∫_0^∞ √(log N(T,d,ε)) dε` as a finite
quantity to be bounded against: `hFinite`, that `T` is totally bounded (`N(T,d,ε)` is finite for
every `ε > 0`, so `Real.log` and `Real.sqrt` are applied to a genuine natural number, not the
junk value from `ℕ∞.toNat ⊤ = 0`); and `hInt`, that the resulting integrand is integrable on
`Set.Ioi 0` (the book's own remark, unstated as a hypothesis but true for every totally bounded
`(T,d)`, that the integrand vanishes once `ε ≥ diam T`, since then a single ball covers `T` and
`N(T,d,ε) = 1`, so `log 1 = 0`). `[Nonempty T]` guards against the degenerate empty index set
(trap 6): every `ε`-net of `T` then has cardinality `≥ 1`, so `N(T,d,ε) ≥ 1` and `Real.log` is
never evaluated at a non-positive argument by way of an empty `T`. The constant `C` is
existentially quantified before every type and hypothesis it is uniform over (trap 8), matching
the book's own "absolute constant" `C`. -/
theorem dudley_integral_inequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {T : Type} [MetricSpace T] [Nonempty T] (X : T → Ω → ℝ)
        (K : ℝ), 0 ≤ K →
        (∀ t, Integrable (X t) P ∧ ∫ ω, X t ω ∂P = 0) →
        (∀ t s, HighDimProb.Concentration.subgaussianNorm P (fun ω => X t ω - X s ω) ≤
          K * dist t s) →
        (∀ ε : ℝ, 0 < ε → coveringNumber T ε < ⊤) →
        IntegrableOn (fun ε => Real.sqrt (Real.log ((coveringNumber T ε).toNat : ℝ)))
          (Set.Ioi (0 : ℝ)) volume →
        processESup P X ≤
          ((C * K *
              ∫ ε in Set.Ioi (0 : ℝ), Real.sqrt (Real.log ((coveringNumber T ε).toNat : ℝ))) :
            EReal) := by sorry

end HighDimProb.Chaining
