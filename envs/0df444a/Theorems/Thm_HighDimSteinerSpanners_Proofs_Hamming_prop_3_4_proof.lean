-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_Hamming_prop_3_4_proof
-- name    : HighDimSteinerSpanners.Proofs.Hamming.prop_3_4_proof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:30.539463+00:00
-- url     : https://prove2.me/theorems/005e9581-5948-4283-adfd-b2c3608b0581
-- title:
--   Hamming: prop 3 4 proof
-- statement:
--   **Proposition 3.4 (Three-Hop Collapse on High-Rate Hypercube Subsets)**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Hamming.lean#L1629-L1815
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Hamming.lean#L1629-L1815

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

theorem HighDimSteinerSpanners.Proofs.Hamming.prop_3_4_proof :
    ∀ (p : ℝ), 1 ≤ p →
      ((∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ d : ℕ, 1 ≤ d →
            ∀ P : Finset (Fin d → Bool),
              2 ≤ P.card →
              (2 : ℝ) ^ ((1 - ε) * (d : ℝ)) ≤ (P.card : ℝ) →
              (∃ (S : Finset (Fin d → Bool)),
                Disjoint P S ∧
                ∃ H : SimpleGraph ↥(P ∪ S),
                  let w := cubeSubgraphWeight p (P ∪ S)
                  Nat.card H.edgeSet ≤ 2 * P.card ∧
                  (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                    ENNReal.ofReal (cubeLpDist p x y) ≤
                      graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                        ⟨y, Finset.mem_union_left S hy⟩) ∧
                  (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                    (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                    (hammingDist x y : ℝ) ≤ ρ * (d : ℝ) →
                    ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                        ⟨y, Finset.mem_union_left S hy⟩,
                      q.IsPath ∧ q.length ≤ 3 ∧
                      walkWeight w q ≤ 5760 * cubeLpDist p x y)) ∧
              ((∀ x ∈ P, ∀ y ∈ P, x ≠ y →
                  (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ)) →
                ∃ (S : Finset (Fin d → Bool)),
                  Disjoint P S ∧
                  ∃ H : SimpleGraph ↥(P ∪ S),
                    let w := cubeSubgraphWeight p (P ∪ S)
                    (Nat.card H.edgeSet : ℝ) ≤ 2 * (P.card : ℝ) * Real.logb 2 (2 / ρ) ∧
                    (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                      ENNReal.ofReal (cubeLpDist p x y) ≤
                        graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                          ⟨y, Finset.mem_union_left S hy⟩) ∧
                    (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P), x ≠ y →
                      ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                          ⟨y, Finset.mem_union_left S hy⟩,
                        q.IsPath ∧ q.length ≤ 3 ∧
                        walkWeight w q ≤ 5760 * cubeLpDist p x y))) ∧
      (∀ d : ℕ, 2 ≤ d →
        ∃ H : SimpleGraph (Fin d → Bool),
          let w : Sym2 (Fin d → Bool) → ℝ :=
            Sym2.lift ⟨fun u v => cubeLpDist p u v, fun u v => by
              simp only [cubeLpDist, lpDist, abs_sub_comm]⟩
          (Nat.card H.edgeSet : ℝ) ≤ 4 * (2 : ℝ) ^ d * Real.logb 2 (d : ℝ) ∧
          (∀ x y : Fin d → Bool, ENNReal.ofReal (cubeLpDist p x y) ≤ graphDist H w x y) ∧
          (∀ x y : Fin d → Bool, x ≠ y →
            ∃ q : H.Walk x y,
              q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w q ≤ 5760 * cubeLpDist p x y))) := by sorry
