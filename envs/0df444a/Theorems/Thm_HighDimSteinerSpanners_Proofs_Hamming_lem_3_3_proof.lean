-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Hamming_lem_3_3_proof
-- name    : HighDimSteinerSpanners.Proofs.Hamming.lem_3_3_proof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:14.97746+00:00
-- url     : https://prove2.me/theorems/617490e1-3dc0-4e8f-baca-f70f85a023e4
-- title:
--   Hamming: lem 3 3 proof
-- statement:
--   **Lemma 3.3 (Single-Scale Blockwise Hamming-Code Hubs)**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Hamming.lean#L846-L1056
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Hamming.lean#L846-L1056

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Hamming
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Hamming

theorem HighDimSteinerSpanners.Proofs.Hamming.lem_3_3_proof :
    ∀ (r d : ℕ), 4 ≤ r → 1 ≤ d →
      ∀ (p : ℝ), 1 ≤ p →
        let b_r : ℝ := (2 : ℝ) ^ r - 1
        let ρ_r : ℝ := 1 / (64 * b_r)
        ∀ (P : Finset (Fin d → Bool)),
          2 ≤ P.card →
          (2 : ℝ) ^ ((1 - (r : ℝ) / (2 * b_r)) * (d : ℝ)) ≤ (P.card : ℝ) →
          ∃ (S_r : Finset (Fin d → Bool)),
            Disjoint P S_r ∧
            ∃ (H_r : SimpleGraph ↥(P ∪ S_r)),
              let w := cubeSubgraphWeight p (P ∪ S_r)
              Nat.card H_r.edgeSet ≤ 2 * P.card ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                ENNReal.ofReal (cubeLpDist p x y) ≤
                  graphDist H_r w ⟨x, Finset.mem_union_left S_r hx⟩
                    ⟨y, Finset.mem_union_left S_r hy⟩) ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                (1 : ℝ) / 3 * ρ_r * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                (hammingDist x y : ℝ) ≤ (9 : ℝ) / 4 * ρ_r * (d : ℝ) →
                ∃ q : H_r.Walk ⟨x, Finset.mem_union_left S_r hx⟩
                    ⟨y, Finset.mem_union_left S_r hy⟩,
                  q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w q ≤ 387 * cubeLpDist p x y) := by sorry
