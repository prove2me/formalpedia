-- Prove2me | Theorems.Thm_MDPFinance_Semicontinuous_continuity_maximizer_existence
-- name    : MDPFinance.Semicontinuous.continuity_maximizer_existence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T20:27:03.24364+00:00
-- url     : https://prove2.me/theorems/32192229-7920-49c9-af54-24d1de05f6df
-- title:
--   Proposition 2.4.8 — continuity is preserved by $T_n$ under a compact, continuous action correspondence
-- statement:
--   Let $v \in \mathrm{IB}_b^+$ be continuous, and suppose: (i) $D_n(x)$ is compact for every
--   $x \in E$ and $x \mapsto D_n(x)$ is continuous; (ii) $(x,a) \mapsto L_n v(x,a)$ is continuous
--   on $D_n$. Then $T_n v$ is continuous, $v$ has a maximizer $f_n \in F_n$ at time $n$, and if $v$
--   has a *unique* maximizer at time $n$, that maximizer is continuous.
--
--   This is the continuous analogue of Proposition 2.4.3: replacing "upper semicontinuous" by
--   "continuous" throughout strengthens the conclusion from upper semicontinuity of $T_n v$ to full
--   continuity, and — new content not present in the upper-semicontinuous case — yields continuity
--   of the maximizer itself whenever it is unique, since a unique maximizer's graph is then a
--   closed, single-valued, upper-semicontinuous correspondence.
--
--   **Formalization Note.** "If $v$ has a unique maximizer $f_n$, then $f_n$ is continuous" is
--   formalized as: any maximizer $f$ that is the *only* maximizer of $v$ at time $n$ (every other
--   maximizer equals it) is continuous — the same content as the book's conditional statement,
--   without introducing a separate "the unique maximizer" notation.
--
--   **Formalization Note (moderation).** Section 2.4 assumes "for the rest of Section 2.4 that
--   $E$ and $A$ are Borel spaces" (Borel subsets of Polish spaces): the sequential arguments and
--   the projection/selection theorems behind these results need separable metrizable spaces with
--   standard Borel σ-algebras, which are now carried as instance hypotheses.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 32, Proposition 2.4.8

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
import Definitions.Def_MDPFinance_Semicontinuous_SetValued

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Proposition 2.4.8 (Bäuerle–Rieder, p. 32, PDF 47): let `v ∈ IB_b^+` be continuous. Suppose
(i) `D_n(x)` is compact for all `x ∈ E` and `x ↦ D_n(x)` is continuous, (ii)
`(x,a) ↦ L_n v(x,a)` is continuous on `D_n`. Then `T_n v` is continuous, there exists a
maximizer `f_n ∈ F_n` of `v`, and if `v` has a unique maximizer `f_n ∈ F_n` at time `n`, then
`f_n` is continuous — formalized as: any maximizer that is the *only* maximizer is
continuous. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem continuity_maximizer_existence {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b) (hv_cont : Continuous v)
    (hD_compact : ∀ x, IsCompact (M.Dx n x)) (hD_cont : ContinuousSetValued (M.Dx n))
    (hL_cont : ContinuousOn (fun p : E × A => L M n v p) (M.D n)) :
    Continuous (T M n v) ∧ (∃ f, IsMaximizer M n v f) ∧
    (∀ f, IsMaximizer M n v f → (∀ f', IsMaximizer M n v f' → f' = f) → Continuous f) := by sorry

end MDPFinance.Semicontinuous
