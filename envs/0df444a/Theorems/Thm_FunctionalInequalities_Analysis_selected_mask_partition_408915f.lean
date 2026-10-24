-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_selected_mask_partition_408915f
-- name    : FunctionalInequalities.Analysis.selected_mask_partition_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:30.047965+00:00
-- url     : https://prove2.me/theorems/65611267-acda-4242-ae53-9dd96164e25d
-- title:
--   Boolean Mask Partition of Derivative Directions
-- statement:
--   This is a combinatorial lemma for the ordered selection operation `selected`.
--
--   For any type $E$, any $m\in\mathbb N$, any list of directions $h:\operatorname{Fin}(m)\to E$, and any Boolean mask $q:\operatorname{Fin}(m)\to\{\mathrm{false},\mathrm{true}\}$:
--
--   1. The lengths of the selected and complementary lists add to $m$.
--   2. Their concatenation is a permutation of `List.ofFn h`.
--   3. The mask selecting exactly one fixed index $i$ produces the singleton list $[h_i]$.
--   4. If `selected h q` has length $1$, then $q$ is the indicator of some single index.
--
--   The result is purely combinatorial and supports the subset bookkeeping in higher-order Leibniz expansions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L172-L294 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.Bilinear`, declaration `FunctionalInequalities.Analysis.selected_mask_partition`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.selected_mask_partition_408915f {E : Type*} {m : ℕ}
    (h : Fin m → E) (q : Fin m → Bool) :
    (selected h q).length + (selected h (fun i => !(q i))).length = m ∧
    (selected h q ++ selected h (fun i => !(q i))).Perm (List.ofFn h) ∧
    (∀ i : Fin m, selected h (fun j => decide (j = i)) = [h i]) ∧
    ((selected h q).length = 1 → ∃ i : Fin m, q = fun j => decide (j = i)) := by sorry
