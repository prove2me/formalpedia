-- Prove2me | Theorems.Thm_MDPFinance_Semicontinuous_measurable_maximizer_existence
-- name    : MDPFinance.Semicontinuous.measurable_maximizer_existence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T20:26:45.437378+00:00
-- url     : https://prove2.me/theorems/7764e0a7-b38e-41c8-b5f7-fc949aa8fffa
-- title:
--   Proposition 2.4.11 — measurability is preserved by $T_n$ with no topology on $D_n(\cdot)$
-- statement:
--   Let $v \in \mathrm{IB}_b^+$, and suppose: (i) $D_n(x)$ is compact for every $x \in E$; (ii)
--   $a \mapsto L_n v(x,a)$ is upper semicontinuous on $D_n(x)$, for every $x \in E$. Then $T_n v$
--   is measurable, and $v$ has a maximizer $f_n \in F_n$ at time $n$.
--
--   Unlike Proposition 2.4.3, no continuity assumption is placed on the set-valued map
--   $x \mapsto D_n(x)$ itself — only that each fiber $D_n(x)$ is compact — and correspondingly the
--   conclusion is weakened from semicontinuity of $T_n v$ to bare measurability. The proof uses a
--   projection theorem of Kunugui and Novikov: $\{x : T_n v(x) \ge \alpha\}$ is the projection onto
--   $E$ of a Borel, compact-valued subset of $D_n$, hence Borel. This proposition is what the goal
--   of this mission, Theorem 2.4.13, invokes directly.
--
--   **Formalization Note.** Hypothesis (ii) is stated fiberwise, as upper semicontinuity of
--   $a \mapsto L_n v(x,a)$ on $D_n(x)$ for each fixed $x$ — a function of the action alone — not
--   jointly in $(x,a)$, exactly as the book's own "$a \mapsto \dots$" notation indicates.
--
--   **Formalization Note (moderation).** Section 2.4 assumes "for the rest of Section 2.4 that
--   $E$ and $A$ are Borel spaces" (Borel subsets of Polish spaces): the sequential arguments and
--   the projection/selection theorems behind these results need separable metrizable spaces with
--   standard Borel σ-algebras, which are now carried as instance hypotheses.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 33, Proposition 2.4.11

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Proposition 2.4.11 (Bäuerle–Rieder, p. 33, PDF 48): let `v ∈ IB_b^+` and suppose (i)
`D_n(x)` is compact for all `x ∈ E`, (ii) `a ↦ L_n v(x,a)` is upper semicontinuous on `D_n(x)`
for all `x ∈ E`. Then `T_n v` is measurable and there exists a maximizer `f_n ∈ F_n` of `v`.
No topology on `D_n(·)` as a set-valued map is assumed here, unlike Proposition 2.4.3/Theorem
2.4.6 — only pointwise compactness of each fiber `D_n(x)`, which is exactly what makes this
the proposition Theorem 2.4.13 (the goal) invokes directly. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem measurable_maximizer_existence {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b)
    (hD_compact : ∀ x, IsCompact (M.Dx n x))
    (hL_usc : ∀ x, UpperSemicontinuousOn (fun a => L M n v (x, a)) (M.Dx n x)) :
    Measurable (T M n v) ∧ ∃ f, IsMaximizer M n v f := by sorry

end MDPFinance.Semicontinuous
