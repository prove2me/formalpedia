-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Bucketing_prop_3_1_proof
-- name    : HighDimSteinerSpanners.Proofs.Bucketing.prop_3_1_proof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:12.068801+00:00
-- url     : https://prove2.me/theorems/69020049-9591-4cfc-b6b2-90cc20848020
-- title:
--   Bucketing: prop 3 1 proof
-- statement:
--   **Proposition 3.1 (Diameter-Bounded Bucketings as `2`-Hop Non-Metric Steiner Spanners)**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Bucketing.lean#L110-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Bucketing.lean#L110-L201

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Bucketing
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Bucketing

theorem HighDimSteinerSpanners.Proofs.Bucketing.prop_3_1_proof :
    ∀ (P : Type) [MetricSpace P] [Fintype P],
      2 ≤ Fintype.card P →
      ∀ (C : ℝ), 1 ≤ C →
        ∀ (I : Type) [Fintype I] (B : I → Finset P),
          (∀ i : I, 2 ≤ (B i).card) →
          (Nat.card (bucketingGraph B).edgeSet = ∑ i : I, (B i).card ∧
            ∀ x y : P,
              ENNReal.ofReal (dist x y) ≤
                graphDist (bucketingGraph B) (bucketingWeight B) (.inl x) (.inl y)) ∧
          ((∀ x y : P, x ≠ y → ∃ i : I, x ∈ B i ∧ y ∈ B i ∧ bucketDiam (B i) ≤ C * dist x y) →
            IsGeneralNonMetricSteinerSpanner C (bucketingGraph B) (bucketingWeight B) ∧
            ∀ x y : P, x ≠ y →
              ∃ q : (bucketingGraph B).Walk (.inl x) (.inl y),
                q.IsPath ∧ q.length ≤ 2 ∧
                walkWeight (bucketingWeight B) q ≤ C * dist x y) := by sorry
