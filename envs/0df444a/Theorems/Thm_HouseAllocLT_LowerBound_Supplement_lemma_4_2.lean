-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_2
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:15:56.74612+00:00
-- url     : https://prove2.me/theorems/ac494162-b395-4b43-94f4-39428d7728c4
-- title:
--   Lemma 4.2 — adding an agent keeps the optimal size and the essential objects
-- statement:
--   In the class-entry setting of §4.2, let a new problem arise from an old one by adding one agent $i$ with any allowed classes, its entries inserted anywhere while the old entries keep their relative order. Then:
--
--   1. every optimum of the new problem is at least as large as every optimum of the old problem;
--   2. every object essential in the old problem is essential in the new one;
--   3. if some new optimum $M_1$ leaves $i$ unmatched, then for every old optimum $M_0$ and every old entry, $M_1$ and $M_0$ have the same value at that entry (every old agent keeps its old optimal class choice).
--
--   The lemma drives the deletion argument of Lemma 4.5 and the essential-object step of Lemma 4.7.
--
--   Differences from the source:
--   - encoding: "the optimal matching size" and "old optimal class choice" → stated for every old optimum and every new optimum; reason: all optima of a problem share one class vector (PDF p. 11), so the statements coincide
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.2, PDF p. 11 (printed p. 9); setting in the preceding paragraph; proof PDF p. 16 (printed p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_ClassEntry

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.2, PDF p. 11 (printed p. 9). Adding one agent `i` with any allowed classes, its
entries inserted anywhere while the old entries keep their relative order: the optimal matching
size cannot decrease, every old essential object remains essential, and if the added agent is
unmatched in a new optimum, every old agent keeps its old optimal class choice. -/
theorem lemma_4_2 {ι α : Type} [Fintype ι] [Fintype α]
    (old new : ClassEntryProblem ι α) (i : ι) (hadd : old.AddsAgent new i) :
    (∀ M₀ M₁ : Finset (ι × α), old.IsOptimum M₀ → new.IsOptimum M₁ → M₀.card ≤ M₁.card) ∧
    (∀ a : α, old.IsEssential a → new.IsEssential a) ∧
    (∀ M₀ M₁ : Finset (ι × α), old.IsOptimum M₀ → new.IsOptimum M₁ → (¬ ∃ a, (i, a) ∈ M₁) →
      ∀ e ∈ old.entries, ClassEntryProblem.entryVal M₁ e = ClassEntryProblem.entryVal M₀ e) := by sorry

end HouseAllocLT.LowerBound.Supplement
