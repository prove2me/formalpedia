-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_thm_2_1a_metric_nearest_terminal_projection
-- name    : HighDimSteinerSpanners.thm_2_1a_metric_nearest_terminal_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:53:38.262799+00:00
-- url     : https://prove2.me/theorems/1a0bb695-4463-4c0b-8bc4-39f9af215e8f
-- title:
--   High Dim Steiner Spanners: thm 2 1a metric nearest terminal projection
-- statement:
--   The High Dim Steiner Spanners construction uses the thm 2 1a metric nearest terminal projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L51-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L51-L63

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

theorem HighDimSteinerSpanners.thm_2_1a_metric_nearest_terminal_projection :
    ∀ (P : Type) [MetricSpace P] [Fintype P],
      2 ≤ Fintype.card P →
      ∀ (C r : ℝ), 1 ≤ C → 0 < r →
        ∀ (S : Type) [Fintype S]
          (H : SimpleGraph (P ⊕ S)) (w : Sym2 (P ⊕ S) → ℝ),
          IsGeneralNonMetricSteinerSpanner C H w →
          ∃ G_hat : SimpleGraph P,
            Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
            (∀ a b : P, G_hat.Adj a b → 0 < dist a b ∧ dist a b ≤ C * r) ∧
            (∀ x y : P, 0 < dist x y → dist x y ≤ r →
              ∃ q : G_hat.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, dist x z ≤ C * r) := by sorry
