-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Combinatorics_thm_2_2b_proof
-- name    : HighDimSteinerSpanners.Proofs.Combinatorics.thm_2_2b_proof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:17.922235+00:00
-- url     : https://prove2.me/theorems/052b1b69-c093-4d8e-8aaa-46fc6fb4bcfd
-- title:
--   Combinatorics: thm 2 2b proof
-- statement:
--   **Theorem 2.2(b) (Biclique Bottleneck Lemma, Module 2)**
--   Note: `HighDimSteinerSpanners.Proofs.Glue.lem_5_1_proof` provides Lemma 5.1
--       (`lem_5_1_interval_crossing`) ready to use.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Combinatorics.lean#L469-L677
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Combinatorics.lean#L469-L677

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Glue
public import Definitions.Def_LeanPool_SteinerSpanners_Combinatorics
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Combinatorics

theorem HighDimSteinerSpanners.Proofs.Combinatorics.thm_2_2b_proof :
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
