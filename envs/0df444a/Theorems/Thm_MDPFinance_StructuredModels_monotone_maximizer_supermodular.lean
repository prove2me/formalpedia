-- Prove2me | Theorems.Thm_MDPFinance_StructuredModels_monotone_maximizer_supermodular
-- name    : MDPFinance.StructuredModels.monotone_maximizer_supermodular
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:36:55.518831+00:00
-- url     : https://prove2.me/theorems/76fc3a2b-e73a-4dc8-a5cd-b818852c3247
-- title:
--   Proposition 2.4.16 — monotone maximizers via supermodularity
-- statement:
--   Let $v \in \mathbb{I\!B}_b^+$ and $D_n^*(x) := \{a \in D_n(x) : L_n v(x,a) = T_n v(x)\}$.
--   Suppose (i) $D_n$ is completely monotone; (ii) $L_n v$ is supermodular on $D_n$; (iii) there is
--   a **largest maximizer** $f_n^*$ of $v$, meaning $f_n^*(x) \geq a$ for every $a \in D_n^*(x)$
--   comparable to $f_n^*(x)$. Then $f_n^*$ is weakly increasing: $x \leq x'$ implies $f_n^*(x)
--   \leq f_n^*(x')$ whenever the two values are comparable.
--
--   **Formalization Note.** Hypothesis (iii) asks for the *largest* maximizer specifically, not
--   merely the existence of *some* increasing maximizer selection — a materially weaker claim the
--   formalization must not substitute for it; `hfstar_largest` states exactly this dominance
--   property. $E$, $A$ are given `Lattice` structure (needed for `⊓`/`⊔` inside supermodularity);
--   see `MODERATION_NOTES.md`.
--
--   **Formalization Note (moderation).** As in the book, $v \in \mathbb{I\!B}_b^+$ and the
--   largest maximizer $f_n^*$ is itself a maximizer of $v$ (`hfstar`), on top of the dominance
--   property; an arbitrary decision rule dominating $D_n^*(x)$ need not select from it.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 35, Proposition 2.4.16

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_CompletelyMonotone
import Definitions.Def_MDPFinance_StructuredModels_Supermodular

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

/-- Proposition 2.4.16 (Bäuerle–Rieder, p. 35, PDF 50). Let `v ∈ IB_b^+` and suppose the
following assumptions are satisfied, where `D_n^*(x) := {a ∈ D_n(x) | L_n v(x,a) = T_n v(x)}` for
`x ∈ E`: (i) `D_n` is completely monotone; (ii) `L_n v` is supermodular on `D_n`; (iii) there
exists a largest maximizer `f_n^*` of `v`, i.e. a maximizer `f_n^*` of `v` such that for all `x ∈ E`
it holds `f_n^*(x) ≥ a` for all `a ∈ D_n^*(x)` which are comparable with `f_n^*(x)`. Then `f_n^*` is weakly increasing, i.e.
`x ≤ x'` implies `f_n^*(x) ≤ f_n^*(x')`, whenever `f_n^*(x)` and `f_n^*(x')` are comparable. -/
theorem monotone_maximizer_supermodular {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [Lattice E] [Lattice A] {N : ℕ} (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b)
    (hCM : CompletelyMonotone (M.D n))
    (hSM : SupermodularOn (M.D n) (L M n v))
    (fstar : E → A)
    (hfstar : IsMaximizer M n v fstar)
    (hfstar_largest : ∀ x : E, ∀ a ∈ {a ∈ M.Dx n x | L M n v (x, a) = T M n v x},
      (fstar x ≤ a ∨ a ≤ fstar x) → a ≤ fstar x) :
    ∀ x x' : E, x ≤ x' → (fstar x ≤ fstar x' ∨ fstar x' ≤ fstar x) → fstar x ≤ fstar x' := by sorry

end MDPFinance.StructuredModels
