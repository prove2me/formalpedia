-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_prop_3_2_simplex_separation
-- name    : HighDimSteinerSpanners.prop_3_2_simplex_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:53:43.306613+00:00
-- url     : https://prove2.me/theorems/20887753-82af-4e54-8a65-b1f667e2a414
-- title:
--   High Dim Steiner Spanners: prop 3 2 simplex separation
-- statement:
--   The High Dim Steiner Spanners construction uses the prop 3 2 simplex separation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L275-L305
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners.lean#L275-L305

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

theorem HighDimSteinerSpanners.prop_3_2_simplex_separation :
    ∀ (p : ℝ), 1 ≤ p →
      (∀ n : ℕ, 3 ≤ n →
        (∀ (C : ℝ), 1 ≤ C → C < 2 →
          ∀ G : SimpleGraph (Fin n),
            IsGeometricSpanner p (stdBasis n) C G →
            Nat.card G.edgeSet = Nat.choose n 2) ∧
        (∃ (S : Type) (_ : Fintype S)
            (H : SimpleGraph (Fin n ⊕ S)) (w : Sym2 (Fin n ⊕ S) → ℝ),
          IsNonMetricSteinerSpanner p (stdBasis n) 1 H w ∧
          Nat.card H.edgeSet = n ∧
          ∀ i j : Fin n, i ≠ j →
            ∃ q : H.Walk (.inl i) (.inl j),
              q.IsPath ∧ q.length ≤ 2 ∧
              walkWeight w q ≤ 1 * lpDist p (stdBasis n i) (stdBasis n j))) ∧
      (∀ (N q r₀ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ r₀ →
        ∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → r₀ ≤ hammingDist x y) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            let stretch : ℝ := ((N : ℝ) / (r₀ : ℝ)) ^ (1 / p)
            ∃ (S : Type) (_ : Fintype S)
              (H : SimpleGraph (Fin X.card ⊕ S)) (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P stretch H w ∧
              Nat.card H.edgeSet = X.card ∧
              ∀ i j : Fin X.card, i ≠ j →
                ∃ q : H.Walk (.inl i) (.inl j),
                  q.IsPath ∧ q.length ≤ 2 ∧
                  walkWeight w q ≤ stretch * lpDist p (P i) (P j)) := by sorry
