-- Prove2me | Theorems.Thm_MDPFinance_Semicontinuous_san_compact_action
-- name    : MDPFinance.Semicontinuous.san_compact_action
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T20:28:22.8354+00:00
-- url     : https://prove2.me/theorems/e30b19ca-cde0-4d09-ad4f-8cf2cde2026f
-- title:
--   Theorem 2.4.13 (GOAL) — the Structure Assumption from pointwise compactness alone
-- statement:
--   Suppose the Markov Decision Model has an upper bounding function $b$, and for every
--   $n = 0,\dots,N-1$: (i) $D_n(x)$ is compact for every $x \in E$; (ii) $a \mapsto \int v(x')\,
--   Q_n(dx' \mid x,a)$ is upper semicontinuous on $D_n(x)$, for every $v \in \mathrm{IB}_b^+$ and
--   every $x \in E$; (iii) $a \mapsto r_n(x,a)$ is upper semicontinuous on $D_n(x)$, for every
--   $x \in E$. Then $\mathrm{IM}_n := \mathrm{IB}_b^+$ and $\Delta_n := F_n$ satisfy the Structure
--   Assumption (SAN).
--
--   This is the weakest — and in that precise sense the deepest — of the section's three
--   "compactness implies (SAN)" theorems. Theorem 2.4.6 and Theorem 2.4.10 both require the
--   set-valued map $x \mapsto D_n(x)$ itself to vary semicontinuously or continuously with $x$;
--   here only *pointwise* compactness of each fiber $D_n(x)$ is assumed, with upper semicontinuity
--   required only in the action variable $a$, at each fixed $x$ separately. Correspondingly the
--   conclusion is the largest possible regularity class, $\mathrm{IM}_n = \mathrm{IB}_b^+$ itself
--   (no semicontinuity survives), obtained via Proposition 2.4.11's measurable-selection argument
--   rather than the sequential compactness argument of Proposition 2.4.3. Combined with chunk
--   `02a-model-bellman-equation`'s Theorem 2.3.8, this is a genuine, checkable sufficient condition
--   for the Bellman equation and existence of an optimal policy to hold on a general Borel state
--   and action space — the generalization has no finite-state-and-action-space analogue on the
--   platform, since compactness and semicontinuity are automatic (and hence contentless) whenever
--   $A$ is finite. A trivializing formalization that specialized $A$ to a finite type, or $D_n(x)$
--   to a single fixed compact set independent of $x$, would collapse the theorem to a case where
--   hypotheses (i)-(iii) hold vacuously; neither specialization is made here.
--
--   **Formalization Note.** Hypotheses (ii)-(iii) are stated fiberwise (as functions of $a$ alone,
--   on $D_n(x)$ at each fixed $x$), matching the book's own "$a \mapsto \dots$" phrasing and
--   Proposition 2.4.11's hypothesis exactly — not jointly in $(x,a)$ on the graph $D_n$, which
--   would be Theorem 2.4.6's strictly stronger hypothesis.
--
--   **Formalization Note (moderation).** Section 2.4 assumes "for the rest of Section 2.4 that
--   $E$ and $A$ are Borel spaces" (Borel subsets of Polish spaces): the sequential arguments and
--   the projection/selection theorems behind these results need separable metrizable spaces with
--   standard Borel σ-algebras, which are now carried as instance hypotheses.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 34, Theorem 2.4.13

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_StructureAssumption
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Theorem 2.4.13 (Bäuerle–Rieder, p. 34, PDF 49), the GOAL of this mission: suppose a Markov
Decision Model with upper bounding function `b` is given and for all `n = 0, …, N-1` it holds:
(i) `D_n(x)` is compact for all `x ∈ E`, (ii) `a ↦ ∫ v(x') Q_n(dx'|x,a)` is upper
semicontinuous for all `v ∈ IB_b^+` and for all `x ∈ E`, (iii) `a ↦ r_n(x,a)` is upper
semicontinuous for all `x ∈ E`. Then the sets `IM_n := IB_b^+` and `Δ_n := F_n` satisfy the
Structure Assumption (SAN). This is the weakest of the section's three "compactness implies
(SAN)" theorems: unlike Theorem 2.4.6 (chunk milestone `san_upper_semicontinuous`) and Theorem
2.4.10 (`san_continuous`), no continuity or semicontinuity of the set-valued map `x ↦ D_n(x)`
itself is assumed, only compactness of each fiber `D_n(x)` — and correspondingly `IM_n` is the
*whole* of `IB_b^+`, not a semicontinuous or continuous subset of it. Following the book's own
remark that this theorem "follows directly from Proposition 2.4.11" (`measurable_maximizer_
existence`), hypotheses (ii)/(iii) are stated exactly as `a ↦ ⋯` functions of the action alone,
at each fixed `x`, on the fiber `D_n(x)` — not jointly in `(x,a)` on the graph `D_n`, which
would be Theorem 2.4.6's strictly stronger hypothesis. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem san_compact_action {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb)
    (hD_compact : ∀ n < N, ∀ x, IsCompact (M.Dx n x))
    (hQ_usc : ∀ n < N, ∀ v ∈ IBbPlus b, ∀ x,
        UpperSemicontinuousOn (fun a => erealIntegral (M.Q n (x, a)) v) (M.Dx n x))
    (hr_usc : ∀ n < N, ∀ x, UpperSemicontinuousOn (fun a => M.r n (x, a)) (M.Dx n x)) :
    StructureAssumption M (fun _ => IBbPlus b) (fun n => {f | IsDecisionRule M n f}) := by sorry

end MDPFinance.Semicontinuous
