-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_selected_mask_partition_readable
-- name    : FunctionalInequalities.Analysis.selected_mask_partition_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:59.993151+00:00
-- url     : https://prove2.me/theorems/cf1a6d5b-9b6d-481c-ae20-5dfef1453e3e
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem selected_mask_partition {E : Type*} {m : ℕ}
--       (h : Fin m → E) (q : Fin m → Bool) :
--       (selected h q).length + (selected h (fun i => !(q i))).length = m ∧
--       (selected h q ++ selected h (fun i => !(q i))).Perm (List.ofFn h) ∧
--       (∀ i : Fin m, selected h (fun j => decide (j = i)) = [h i]) ∧
--       ((selected h q).length = 1 → ∃ i : Fin m, q = fun j => decide (j = i))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/IteratedDerivative/Bilinear`](https://prove2.me/theorems/c2e12327-8e36-4fb7-a6f8-00519f39d229).
--
--   Previous: [`sum_filter_eq_two_mul_sum_filter_of_compl_invariant`](https://prove2.me/theorems/df0e8f70-61ce-476e-a922-0def8bd9c052).
--
--   [Source excerpt, lines 177–182](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L177-L182) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L172-L294 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.Bilinear`, declaration `FunctionalInequalities.Analysis.selected_mask_partition`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear

theorem FunctionalInequalities.Analysis.selected_mask_partition_readable {E : Type*} {m : ℕ}
    (h : Fin m → E) (q : Fin m → Bool) :
    (selected h q).length + (selected h (fun i => !(q i))).length = m ∧
    (selected h q ++ selected h (fun i => !(q i))).Perm (List.ofFn h) ∧
    (∀ i : Fin m, selected h (fun j => decide (j = i)) = [h i]) ∧
    ((selected h q).length = 1 → ∃ i : Fin m, q = fun j => decide (j = i)) := by sorry
