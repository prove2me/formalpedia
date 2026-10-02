-- Prove2me | Theorems.Thm_MDPFinance_Semicontinuous_san_continuous
-- name    : MDPFinance.Semicontinuous.san_continuous
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T20:29:12.388694+00:00
-- url     : https://prove2.me/theorems/5a1ec6f2-5509-4a40-bee8-5af3acf25a37
-- title:
--   Theorem 2.4.10 — the Structure Assumption under continuity
-- statement:
--   Suppose the Markov Decision Model has an upper bounding function $b$, and for every
--   $n = 0,\dots,N-1$: (i) $D_n(x)$ is compact for all $x$ and $x \mapsto D_n(x)$ is continuous;
--   (ii) $(x,a) \mapsto \int v(x')\, Q_n(dx' \mid x,a)$ is continuous for every continuous
--   $v \in \mathrm{IB}_b^+$; (iii) $(x,a) \mapsto r_n(x,a)$ is continuous; (iv) $x \mapsto g_N(x)$
--   is continuous. Then $\mathrm{IM}_n := \{v \in \mathrm{IB}_b^+ : v \text{ continuous}\}$ and
--   $\Delta_n := F_n$ satisfy the Structure Assumption (SAN).
--
--   The continuous parallel to Theorem 2.4.6, obtained the same way from Proposition 2.4.8 instead
--   of Proposition 2.4.3: the value functions produced under these hypotheses are not merely upper
--   semicontinuous but fully continuous, at the cost of assuming continuity — rather than mere
--   upper semicontinuity — of $x \mapsto D_n(x)$, the kernel integral, the reward, and the terminal
--   payoff throughout.
--
--   **Formalization Note.** The book's closing sentence ("if the maximizer of $V_n$ is unique, then
--   $\Delta_n$ can be chosen as the continuous functions") is about the fixed value function $V_n$
--   of chunk `02a` and is not restated here, for the same reason as in `san_upper_semicontinuous`
--   above (see `MODERATION_NOTES.md`). Hypotheses (ii)-(iii) are required on the graph $D_n$ only.
--
--   **Formalization Note (moderation).** Section 2.4 assumes "for the rest of Section 2.4 that
--   $E$ and $A$ are Borel spaces" (Borel subsets of Polish spaces): the sequential arguments and
--   the projection/selection theorems behind these results need separable metrizable spaces with
--   standard Borel σ-algebras, which are now carried as instance hypotheses.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 33, Theorem 2.4.10

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_StructureAssumption
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
import Definitions.Def_MDPFinance_Semicontinuous_SetValued

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Theorem 2.4.10 (Bäuerle–Rieder, p. 33, PDF 48): suppose a Markov Decision Model with upper
bounding function `b` is given and for all `n = 0, …, N-1` it holds: (i) `D_n(x)` is compact
for all `x ∈ E` and `x ↦ D_n(x)` is continuous, (ii) `(x,a) ↦ ∫ v(x') Q_n(dx'|x,a)` is
continuous for all continuous `v ∈ IB_b^+`, (iii) `(x,a) ↦ r_n(x,a)` is continuous, (iv)
`x ↦ g_N(x)` is continuous. Then the sets `IM_n := {v ∈ IB_b^+ | v` continuous`}` and
`Δ_n := F_n` satisfy the Structure Assumption (SAN). The book's closing sentence, "if the
maximizer of `V_n` is unique, then `Δ_n` can be chosen as the set of continuous functions",
is about the value function `V_n` fixed in chunk `02a` and is not restated here — formalizing
it would require rebuilding that chunk's whole value-function/policy apparatus for a corollary
that is not this theorem's own (SAN) content; see `MODERATION_NOTES.md`. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem san_continuous {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb)
    (hD_compact : ∀ n < N, ∀ x, IsCompact (M.Dx n x))
    (hD_cont : ∀ n < N, ContinuousSetValued (M.Dx n))
    (hQ_cont : ∀ n < N, ∀ v ∈ IBbPlus b, Continuous v →
        ContinuousOn (fun p : E × A => erealIntegral (M.Q n p) v) (M.D n))
    (hr_cont : ∀ n < N, ContinuousOn (M.r n) (M.D n))
    (hg_cont : Continuous M.g) :
    StructureAssumption M (fun _ => {v ∈ IBbPlus b | Continuous v})
      (fun n => {f | IsDecisionRule M n f}) := by sorry

end MDPFinance.Semicontinuous
