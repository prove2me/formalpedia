-- Prove2me | Theorems.Thm_OPG500Counterexample_geodesic_cycle_outside_span
-- name    : OPG500Counterexample.geodesic_cycle_outside_span
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T04:08:24.80369+00:00
-- url     : https://prove2.me/theorems/f36a45fc-0573-4e2e-b81a-7d0088f00309
-- title:
--   A geodesic cycle outside a closed binary family
-- statement:
--   Let $G$ be a finite simple graph with strictly positive real edge weights, and let `inside` be a predicate on binary edge vectors that is closed under addition. Assume a finite list contains every simple cycle of $G$ and at least one cycle has its edge vector outside `inside`.
--
--   If every nongeodesic cycle splits into two strictly shorter simple cycles whose binary edge vectors sum to the original vector, then
--
--   $$
--   \exists C,\quad C\text{ is vertex-geodesic and its edge vector is outside `inside`}.
--   $$
--
--   The statement includes tied cycle lengths and requires strict decrease only for the two cycles supplied by a split.
-- source:
--   Candidate C10, Sections T3 and T6, and candidate C12: https://github.com/vibemathing/problem-opg-500-geodesic-cycles/blob/a41fe59b4535851ea55f6e868e938b9aaf81e924/research/artifacts/candidates/opg500-a01-c10/tight-rank.md; https://github.com/vibemathing/problem-opg-500-geodesic-cycles/blob/a41fe59b4535851ea55f6e868e938b9aaf81e924/research/artifacts/candidates/opg500-a01-c12/FiniteDescent.lean

import Definitions.Def_opg500_weighted_cycle_models

namespace OPG500Counterexample

universe u

/-- A graph-level finite descent principle. If every nongeodesic cycle splits
into two strictly shorter cycles whose binary edge vectors add to the original,
then any closed family missing some cycle also misses a geodesic cycle. -/
theorem geodesic_cycle_outside_span
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : EdgeWeight G) (hpositive : IsPositive ℓ)
    (inside : (Sym2 V → ZMod 2) → Prop)
    (inside_add : ∀ a b, inside a → inside b → inside (a + b))
    (table : List (Cycle G))
    (complete : ∀ C : Cycle G, C ∈ table)
    (outside : ∃ C : Cycle G, ¬ inside C.edgeVector)
    (split : ∀ C : Cycle G, ¬ C.IsGeodesic ℓ →
      ∃ A B : Cycle G,
        Walk.weightedLength ℓ A.walk < Walk.weightedLength ℓ C.walk ∧
        Walk.weightedLength ℓ B.walk < Walk.weightedLength ℓ C.walk ∧
        C.edgeVector = A.edgeVector + B.edgeVector) :
    ∃ C : Cycle G, C.IsGeodesic ℓ ∧ ¬ inside C.edgeVector := by sorry

end OPG500Counterexample
