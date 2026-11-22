-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_prop_3_1_diameter_bounded_bucketing
-- name    : HighDimSteinerSpanners.prop_3_1_diameter_bounded_bucketing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:53:26.11759+00:00
-- url     : https://prove2.me/theorems/bddd47b8-1613-44ea-882f-868ccb397216
-- title:
--   High Dim Steiner Spanners: prop 3 1 diameter bounded bucketing
-- statement:
--   The High Dim Steiner Spanners construction uses the prop 3 1 diameter bounded bucketing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L257-L273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L257-L273

module
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Glue
public import Definitions.Def_LeanPool_SteinerSpanners_Projection
public import Definitions.Def_LeanPool_SteinerSpanners_Combinatorics
public import Definitions.Def_LeanPool_SteinerSpanners_CSP
public import Definitions.Def_LeanPool_SteinerSpanners_Bucketing
public import Definitions.Def_LeanPool_SteinerSpanners_Hamming
public import Definitions.Def_LeanPool_SteinerSpanners_Dvoretzky
public import Definitions.Def_LeanPool_SteinerSpanners
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners

theorem HighDimSteinerSpanners.prop_3_1_diameter_bounded_bucketing :
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
