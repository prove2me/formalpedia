-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_cor_1_4_lp_dvoretzky_lower_bound
-- name    : HighDimSteinerSpanners.cor_1_4_lp_dvoretzky_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:53:44.203224+00:00
-- url     : https://prove2.me/theorems/d151bc7e-a521-4e7b-8c5a-a5ac9b88647f
-- title:
--   High Dim Steiner Spanners: cor 1 4 lp dvoretzky lower bound
-- statement:
--   The High Dim Steiner Spanners construction uses the cor 1 4 lp dvoretzky lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L229-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L229-L255

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

theorem HighDimSteinerSpanners.cor_1_4_lp_dvoretzky_lower_bound :
    ∃ (M : ℝ) (c c₀ A : ℝ → ℝ),
      0 < M ∧
      (∀ C : ℝ, 1 ≤ C →
        (2 : ℝ) ^ (-M * C ^ (6 : ℕ) * Real.logb 2 (C + 1)) ≤ c C ∧ 0 < c₀ C ∧ 0 < A C) ∧
      ∀ (p : ℝ), 2 < p →
        ∀ (C : ℝ), 1 ≤ C →
          ∃ (β₁ β₂ : ℝ), 0 < β₁ ∧ β₁ ≤ β₂ ∧
            ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
              ∀ j : ℕ,
                ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                  1 ≤ d ∧
                  β₁ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ≤ (d : ℝ) ∧
                  (d : ℝ) ≤ β₂ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ∧
                  Function.Injective P ∧
                  aspectRatio p P ≤ A C ∧
                  (∀ (S : Type) [Fintype S]
                    (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                    (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                    IsNonMetricSteinerSpanner p P C H w →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card H.edgeSet : ℝ)) ∧
                  (∀ (G : SimpleGraph (Fin (nSeq j))),
                    IsGeometricSpanner p P C G →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card G.edgeSet : ℝ)) := by sorry
