-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_main_theorem
-- name    : MatroidProphetKW.Single.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:44.864874+00:00
-- url     : https://prove2.me/theorems/7d10674a-ed13-4b69-bd36-d4087ab42ac5
-- title:
--   Main theorem — against any online weight-adaptive adversary, the threshold algorithm (9) earns $\mathbb E[w(A)] \ge \tfrac12\,\mathrm{OPT}$
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid on a finite ground set, and for each $x \in \mathcal U$ let $F_x$ be a probability distribution supported on $[0, \infty)$ with finite mean. The weights $w(x)$ are independent with $w(x) \sim F_x$, and $\mathrm{OPT} = \mathbb E[\mathrm{OPT}(w)]$ is the expected weight of the maximum-weight independent set.
--
--   An online weight-adaptive adversary reveals the elements one at a time, choosing each next element knowing only the weights already revealed. The algorithm of §3.3, having selected $A_{i-1}$, selects the arriving element $x_i$ if and only if $A_{i-1} \cup \{x_i\} \in \mathcal I$ and
--   $$w(x_i) \;\ge\; \tfrac12\, \mathbb E_{w'}\big[w'(R(A_{i-1})) - w'(R(A_{i-1} \cup \{x_i\}))\big],$$
--   where $w'$ is an independent copy of the weights and $R(\cdot)$ is the remainder of the $w'$-maximum-weight basis (§3.2). Then for every online weight-adaptive adversary, the set $A$ the algorithm selects satisfies
--   $$\mathbb E[w(A)] \;\ge\; \tfrac12\, \mathrm{OPT}.$$
--
--   This is the matroid prophet inequality: on every matroid, an online algorithm facing the elements in an adversarial, adaptively chosen order earns at least half of what a prophet who sees all weights in advance earns. The factor $\tfrac12$ is the best possible already for rank-one matroids (the classical prophet inequality).
--
--   **Formalization Note** The statement is for the paper's own algorithm, which is stronger than the existence statement of §3. The thresholds are fixed by (9), not assumed to satisfy (2)–(3). The adversary is deterministic and measurable in the revealed weights; randomized adversaries are mixtures of these. $\mathbb E[w(A)]$ and $\mathrm{OPT}$ are Bochner integrals under the finite-mean assumption.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 4 (§3, main theorem); Proposition 1, p. 6; (9), p. 7

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Online
import Definitions.Def_MatroidProphetKW_Single_Algorithm

namespace MatroidProphetKW.Single

open MeasureTheory

/-- Main theorem (Kleinberg–Weinberg, arXiv:1201.4764v1, §3, p. 4; Proposition 1, p. 6, with
`α = 2`; algorithm (9), p. 7): against every online weight-adaptive adversary, the algorithm of
§3.3 — select `x_i` iff `A_{i−1} ∪ {x_i} ∈ ℐ` and `w(x_i) ≥ ½ E[w′(R(A_{i−1})) − w′(R(A_{i−1} ∪ {x_i}))]`
— earns `E[w(A)] ≥ ½ · OPT`. -/
theorem main_theorem {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF0 : ∀ x, F x (Set.Iio 0) = 0) (hFi : ∀ x, Integrable id (F x))
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) :
    (1 / 2) * OPT M F ≤ ∫ w, wt w (run M (kwThr M F) (advOrder adv w) w) ∂(Measure.pi F) := by sorry

end MatroidProphetKW.Single
