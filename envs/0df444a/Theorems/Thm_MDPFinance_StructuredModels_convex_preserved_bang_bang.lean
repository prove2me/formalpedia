-- Prove2me | Theorems.Thm_MDPFinance_StructuredModels_convex_preserved_bang_bang
-- name    : MDPFinance.StructuredModels.convex_preserved_bang_bang
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:36:55.555038+00:00
-- url     : https://prove2.me/theorems/72ca787a-48c8-41bd-ba5a-114363509eeb
-- title:
--   Proposition 2.4.21 — $T_n$ preserves convexity; bang-bang maximizer
-- statement:
--   Let $v \in \mathbb{I\!B}_b^+$ and suppose (i) $E$ is convex and $D_n = E \times A$; (ii) $x
--   \mapsto L_n v(x,a)$ is convex for every $a \in A$. Then $T_n v$ is convex on $E$. If moreover
--   $A$ is a **polytope** (compact, convex, finitely many extreme points) and $a \mapsto L_n
--   v(x,a)$ is convex for every $x$, there is a **bang-bang maximizer** $f_n^*$ of $v$: $f_n^*(x)$
--   is a vertex (extreme point) of $A$ for every $x$.
--
--   **Formalization Note.** "$A$ is a polytope" is formalized as $A$ (taken as the whole type,
--   `Set.univ`) compact, convex, with `(Set.univ : Set A).extremePoints ℝ` finite; a vertex is an
--   element of `Set.extremePoints`. Both conclusions of the proposition are proved together under
--   the combined hypothesis set (base convexity plus the polytope/joint-convexity hypotheses),
--   since the goal, Theorem 2.4.22, only ever needs the first conclusion applied to the base
--   hypotheses alone — see `MODERATION_NOTES.md`.
--
--   **Formalization Note (moderation).** The first conclusion ($T_n v$ convex) is asserted under
--   (i)–(ii) alone, and the bang-bang maximizer as an implication from the polytope and
--   joint-convexity hypotheses, exactly as the book states it; the draft had required the extra
--   hypotheses for both.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 37, Proposition 2.4.21

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

/-- Proposition 2.4.21 (Bäuerle–Rieder, p. 37, PDF 52). Let `v ∈ IB_b^+` and suppose (i) `E` is
convex and `D_n := E × A`, (ii) `x ↦ L_n v(x,a)` is convex for all `a ∈ A`. Then `T_n v` is
convex on `E`. If moreover `A` is a polytope (compact, convex, with finitely many extreme
points/vertices) and `a ↦ L_n v(x,a)` is convex for all `x ∈ E`, then there exists a so-called
bang-bang maximizer `f_n^*` of `v` at time `n`, i.e. `f_n^*(x)` is a vertex of `A` for all
`x ∈ E`. The first conclusion holds under (i)-(ii) alone; the second is an implication from the
polytope and joint-convexity hypotheses, as the book states it. -/
theorem convex_preserved_bang_bang {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]
    {N : ℕ} (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b)
    (hDn : M.D n = Set.univ)
    (hL_convex_x : ∀ a : A, ConvexOnEReal Set.univ (fun x => L M n v (x, a))) :
    ConvexOnEReal Set.univ (T M n v) ∧
      (IsCompact (Set.univ : Set A) → Convex ℝ (Set.univ : Set A) →
        ((Set.univ : Set A).extremePoints ℝ).Finite →
        (∀ x : E, ConvexOnEReal Set.univ (fun a => L M n v (x, a))) →
        ∃ f : E → A, IsMaximizer M n v f ∧
          ∀ x : E, f x ∈ (Set.univ : Set A).extremePoints ℝ) := by sorry

end MDPFinance.StructuredModels
