-- Prove2me | Theorems.Thm_LocalLemma_coin_dependency
-- name    : LocalLemma.coin_dependency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:20:28.950895+00:00
-- url     : https://prove2.me/theorems/d5fb1a5f-58f3-4984-a031-42497c8d304d
-- title:
--   Local Lemma: coin dependency
-- statement:
--   Events depending on coordinate sets that are disjoint whenever the indices are non-adjacent
--   form a dependency graph.
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/Coin.lean#L62-L80
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/Coin.lean#L62-L80

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma

theorem LocalLemma.coin_dependency {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Fin n → Set (ι → Bool)) (D : Fin n → Finset ι) (hA : ∀ i, CoordDep (A i) (D i))
    (Γ : SimpleGraph (Fin n)) (hΓ : ∀ i j, j ≠ i → ¬ Γ.Adj i j → Disjoint (D i) (D j)) :
    ∀ i, Indep (MeasurableSpace.generateFrom {A i})
      (MeasurableSpace.generateFrom {s | ∃ j, j ≠ i ∧ ¬ Γ.Adj i j ∧ s = A j})
      (coinMeasure ι) := by sorry
