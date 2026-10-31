-- Prove2me | Theorems.Thm_FoundationsRL_DECLowerExamples_embedded_mab_dec_lower
-- name    : FoundationsRL.DECLowerExamples.embedded_mab_dec_lower
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:22:06.346986+00:00
-- url     : https://prove2.me/theorems/45feb084-2161-4594-ba2c-4e65a18a7bba
-- title:
--   Proposition 30 — bandit embedding gives $\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M,\widehat M)\ge\frac{\alpha}{2}\mathbb I\{\varepsilon\ge\beta/\sqrt N\}$ (corrected: $N\ge2$, distinct $\pi_i$)
-- statement:
--   Let $\widehat M$ be a reference model, and suppose a class $\mathcal M$ contains models $M_1,\dots,M_N$, $N\ge2$, together with pairwise distinct decisions $\pi_1,\dots,\pi_N$, such that for every $i$ and every decision $\pi$:
--
--   1. $D^2_{\mathrm H}\bigl(M_i(\pi),\widehat M(\pi)\bigr)\le\beta^2\cdot\mathbb I\{\pi=\pi_i\}$;
--   2. $f^{M_i}(\pi_{M_i})-f^{M_i}(\pi)\ge\alpha\cdot\mathbb I\{\pi\ne\pi_i\}$,
--
--   where $\alpha,\beta\ge0$. Then for every $\varepsilon$,
--   $$
--   \mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M,\widehat M)\ \ge\ \frac{\alpha}{2}\cdot\mathbb I\bigl\{\varepsilon\ge\beta/\sqrt N\bigr\}.
--   $$
--
--   In words: if $\mathcal M$ contains $N$ models, each of which differs from $\widehat M$ only at its own decision (by at most $\beta^2$ in squared Hellinger distance) and is $\alpha$-suboptimal at every other decision, then the constrained Decision-Estimation Coefficient is of order $\alpha$ as soon as $\varepsilon\ge\beta/\sqrt N$. This is the multi-armed-bandit lower-bound pattern in general form: Examples 6.4 and 6.5 are instances, and Proposition 28 turns it into a lower bound on the minimax regret.
--
--   **Formalization Note** The decision space is any measurable space in which single decisions are events; models are kernels from decisions to measures on $\mathbb R\times\mathcal O$, and $\widehat M$ need not belong to $\mathcal M$. The coefficient and the gap take values in $[0,\infty]$; the indicators are `Set.indicator`.
--
--   Differences from the source:
--   - correction: any N ≥ 1 and a collection of decisions π₁, …, π_N → 2 ≤ N and i ↦ π_i injective; reason: with N = 1, or with all π_i equal, take M₁ = … = M_N with M₁(π) the point mass at reward α·I{π = π₁}, M̂ = M₁, β = 0 and M = {M₁}; both hypotheses hold, and the point mass on π₁ has regret 0 and meets the constraint, so the coefficient is 0 although α·I{ε ≥ 0} = α for α > 0, ε ≥ 0
--   - generalization: dec^c_ε(M, M̂) ≳ α·I{ε ≥ β/√N} → dec^c_ε(M, M̂) ≥ (α/2)·I{ε ≥ β/√N}; reason: an explicit absolute constant 1/2 implies the bound up to an absolute constant
--   - reading: p ∈ Δ(Π), with the masses p(π_i) used in the argument → MeasurableSingletonClass on the decision space, and every model measurable in the decision (a Lean `Kernel`); reason: the notes never fix a σ-algebra on Π; the masses p(π_i) (Example 6.4) presuppose that single decisions are events, and without measurability of π ↦ M(π) and of the singletons the expectations in dec^c are undefined
--   - generalization: models Π → Δ(R × O) and a radius ε > 0 → arbitrary kernels Π → Measure(ℝ × O) and any real ε; reason: the statement is stated for these and specializes to probability kernels and ε > 0
--   - encoding: real α and β, β² a bound on a squared distance → α, β ∈ ℝ≥0; reason: β is a distance, and for α < 0 the source's conclusion is trivially true
--   - encoding: f^M(π_M) − f^M(π) and dec^c real valued, π_M an argmax, expectations → values in [0, ∞], argmax replaced by a supremum, expectations as lower Lebesgue integrals; reason: no reward range is assumed, so the suprema must be representable; these agree with the source whenever the maximum is attained and the integrands are measurable
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 30, p. 111

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_hellingerSq
import Definitions.Def_FoundationsRL_DECLowerExamples_suboptGap
import Definitions.Def_FoundationsRL_DECLowerExamples_constrainedDECRef

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FoundationsRL.DECLowerExamples

/-- **Proposition 30 (a class embedding the multi-armed bandit has `dec^c_ε ≳ α`).** Let a reference
model `M̂` be given, and suppose the class `M` contains a sub-class `{M_1, …, M_N}` with pairwise
distinct decisions `π_1, …, π_N` such that for all `i` and all `π`:
1. `D²_H(M_i(π), M̂(π)) ≤ β² · I{π = π_i}`;
2. `f^{M_i}(π_{M_i}) − f^{M_i}(π) ≥ α · I{π ≠ π_i}`.
Then `dec^c_ε(M, M̂) ≥ (α/2) · I{ε ≥ β/√N}`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Proposition 30, p. 111 (corrected: `N ≥ 2`, decisions distinct).

**Formalization Note.** The notes' `≳` is stated with the explicit constant `1/2`. The printed
statement is false for `N = 1` and for coinciding decisions (the point mass on `π_1` has regret `0`
and meets the constraint), hence `2 ≤ N` and `Function.Injective πs`. `α, β ∈ ℝ≥0` (a gap and a
distance). Decisions are events (`MeasurableSingletonClass`), as `p(π_i)` presupposes. The
indicators are `Set.indicator`; `dec^c` and the gap take values in `[0, ∞]`. Models are arbitrary
kernels `Π → Measure (ℝ × O)` and `M̂` need not belong to `M`. -/
theorem embedded_mab_dec_lower {D O : Type*} [MeasurableSpace D] [MeasurableSingletonClass D]
    [MeasurableSpace O] (Ms : Set (Kernel D (ℝ × O))) (Mhat : Kernel D (ℝ × O))
    (N : ℕ) (hN : 2 ≤ N) (Mi : Fin N → Kernel D (ℝ × O)) (πs : Fin N → D)
    (hMi : ∀ i, Mi i ∈ Ms) (hπs : Function.Injective πs) (α β : ℝ≥0)
    (h1 : ∀ i π, FoundationsRL.DECLower.hellingerSq (Mi i π) (Mhat π) ≤
      ({πs i} : Set D).indicator (fun _ => (β : ℝ≥0∞) ^ 2) π)
    (h2 : ∀ i π, ({πs i}ᶜ : Set D).indicator (fun _ => (α : ℝ≥0∞)) π ≤ suboptGap (Mi i) π)
    (ε : ℝ) :
    (if (β : ℝ) / Real.sqrt N ≤ ε then (α : ℝ≥0∞) / 2 else 0) ≤ constrainedDECRef ε Ms Mhat := by sorry

end FoundationsRL.DECLowerExamples
