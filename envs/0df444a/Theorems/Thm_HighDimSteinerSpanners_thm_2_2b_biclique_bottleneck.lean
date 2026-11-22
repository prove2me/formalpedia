-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_thm_2_2b_biclique_bottleneck
-- name    : HighDimSteinerSpanners.thm_2_2b_biclique_bottleneck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:53:19.544121+00:00
-- url     : https://prove2.me/theorems/3d28b2be-90f7-4cfc-9237-20fcae532169
-- title:
--   High Dim Steiner Spanners: thm 2 2b biclique bottleneck
-- statement:
--   The High Dim Steiner Spanners construction uses the thm 2 2b biclique bottleneck property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L107-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L107-L124

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

theorem HighDimSteinerSpanners.thm_2_2b_biclique_bottleneck :
    ∀ (C₁ rStar N ℓ : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 1 ≤ N → 1 ≤ ℓ →
      ∀ (F : Fin (ℓ + 1) → Finset (Fin N)),
        (∀ i : Fin (ℓ + 1), (F i).card ≤ C₁ * rStar) →
        ((F 0 ∩ F (Fin.last ℓ)).card : ℝ) ≤ (rStar : ℝ) / 4 →
        ∃ (s : Fin ℓ) (k : ℕ), k ≤ 8 * C₁ ∧
          ∃ (t : Fin k → Fin (ℓ + 1)) (A : Fin k → Finset (Fin N)) (I_k : Finset (Fin N)),
            Pairwise (fun i j => Disjoint (A i) (A j)) ∧
            (∀ r : Fin k, Disjoint (A r) I_k) ∧
            Finset.univ.biUnion A ∪ I_k = F s.castSucc ∩ F s.succ ∧
            (I_k.card : ℝ) ≤ (rStar : ℝ) / 2 ∧
            ∀ r : Fin k,
              let I_rem := (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
              Disjoint (A r) (F (t r)) ∧
              I_rem ⊆ F (t r) ∧
              ((A r).card : ℝ) - (rStar : ℝ) / 4 ≤
                ((((F s.castSucc ∪ F s.succ) ∩ F (t r)) \ (A r ∪ I_rem)).card : ℝ) := by sorry
