-- Prove2me | Theorems.Thm_MDPFinance_Semicontinuous_usc_maximizer_existence
-- name    : MDPFinance.Semicontinuous.usc_maximizer_existence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T20:27:22.460984+00:00
-- url     : https://prove2.me/theorems/9be9b1eb-cbf1-42d3-956e-02411d20d965
-- title:
--   Proposition 2.4.3 — upper semicontinuity is preserved by $T_n$ under a compact, u.s.c. action correspondence
-- statement:
--   Let $v \in \mathrm{IB}_b^+$ be upper semicontinuous, and suppose: (i) $D_n(x)$ is compact for
--   every $x \in E$ and $x \mapsto D_n(x)$ is upper semicontinuous; (ii) $(x,a) \mapsto L_n v(x,a)$
--   is upper semicontinuous on $D_n$. Then $T_n v$ is upper semicontinuous, and $v$ has a maximizer
--   $f_n$ at time $n$.
--
--   This is the technical engine behind Theorem 2.4.6: under hypotheses (i)-(ii) here, the
--   supremum defining $T_n v(x) = \sup_{a \in D_n(x)} L_n v(x,a)$ is attained on the compact set
--   $D_n(x)$ (Weierstrass), and the upper semicontinuity of $x \mapsto D_n(x)$ lets the maximizing
--   action be chosen so that $T_n v$ itself stays upper semicontinuous as $x$ varies; a measurable
--   selection of a maximizer then follows from the Kuratowski–Ryll-Nardzewski selection theorem
--   applied to the (compact-valued, Borel) set of maximizers.
--
--   **Formalization Note.** Condition (ii) is stated as `UpperSemicontinuousOn` on the graph
--   $D_n \subseteq E \times A$, matching that $L_n$'s defining data ($r_n$) is itself only assumed
--   regular on $D_n$.
--
--   **Formalization Note (moderation).** Section 2.4 assumes "for the rest of Section 2.4 that
--   $E$ and $A$ are Borel spaces" (Borel subsets of Polish spaces): the sequential arguments and
--   the projection/selection theorems behind these results need separable metrizable spaces with
--   standard Borel σ-algebras, which are now carried as instance hypotheses.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 29-30, Proposition 2.4.3

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
import Definitions.Def_MDPFinance_Semicontinuous_SetValued

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Proposition 2.4.3 (Bäuerle–Rieder, p. 29-30, PDF 44-45): let `v ∈ IB_b^+` be upper
semicontinuous. Suppose (i) `D_n(x)` is compact for all `x ∈ E` and `x ↦ D_n(x)` is upper
semicontinuous, (ii) `(x,a) ↦ L_n v(x,a)` is upper semicontinuous on `D_n`. Then `T_n v` is
upper semicontinuous and there exists a maximizer `f_n` of `v`. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem usc_maximizer_existence {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b) (hv_usc : UpperSemicontinuous v)
    (hD_compact : ∀ x, IsCompact (M.Dx n x)) (hD_usc : USCSetValued (M.Dx n))
    (hL_usc : UpperSemicontinuousOn (fun p : E × A => L M n v p) (M.D n)) :
    UpperSemicontinuous (T M n v) ∧ ∃ f, IsMaximizer M n v f := by sorry

end MDPFinance.Semicontinuous
