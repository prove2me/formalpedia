-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Combinatorics_thm_2_2a_proof
-- name    : HighDimSteinerSpanners.Proofs.Combinatorics.thm_2_2a_proof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:22.768354+00:00
-- url     : https://prove2.me/theorems/2af2128f-84bf-4bde-993d-00765dc88baf
-- title:
--   Combinatorics: thm 2 2a proof
-- statement:
--   **Theorem 2.2(a) (Last-Hit Edge Charging, Module 2)**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Combinatorics.lean#L113-L324
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Combinatorics.lean#L113-L324

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

theorem HighDimSteinerSpanners.Proofs.Combinatorics.thm_2_2a_proof :
    ∀ (C₁ rStar N q K : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 2 ≤ N → 2 ≤ q → 1 ≤ K →
      ∀ (X : Finset (Fin N → Fin q)) (G_hat : SimpleGraph ↥X)
        (L : ↥X → ↥X → Finset ↥X),
        (∀ a b : ↥X, G_hat.Adj a b →
          0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) →
        (∀ x y : ↥X, hammingDist x.val y.val = rStar →
          ∃ q_walk : G_hat.Walk x y,
            q_walk.IsPath ∧ ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar) →
        ListSizeCond C₁ rStar K X L →
        OverlapCond C₁ rStar K X →
        ListHitCond C₁ rStar X L →
        (exactDistPairs X rStar).card ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet := by sorry
