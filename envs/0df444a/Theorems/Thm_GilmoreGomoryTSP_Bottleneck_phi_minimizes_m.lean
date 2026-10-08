-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_Bottleneck_phi_minimizes_m
-- name    : GilmoreGomoryTSP.Bottleneck.phi_minimizes_m
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:23.738983+00:00
-- url     : https://prove2.me/theorems/d34e7df9-e22a-424e-b20d-8639b510a977
-- title:
--   p. 671 — the ranking permutation φ minimizes m over all permutations
-- statement:
--   Let $B_1\le\dots\le B_N$, $f\ge 0$ locally integrable, $g=0$, and let $\varphi$ rank the $A$'s. Then for every permutation $\psi$ of the jobs (tour or not),
--   $$ m(\varphi) = \max_i c_{i\varphi(i)} \;\le\; m(\psi) = \max_i c_{i\psi(i)}.$$
--
--   This is the bottleneck assignment problem (Gross) for the cost matrix (1) with $g=0$, $f\ge0$: the ranking permutation that solves the sum problem also solves the bottleneck problem without the tour constraint.
--
--   **Formalization Note** The cost is (1) with $g$ identically $0$ and $f\ge0$ locally integrable.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 671, "Incidentally this latter argument …"

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

theorem phi_minimizes_m {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)), m f g A B φ ≤ m f g A B ψ := by sorry

end GilmoreGomoryTSP.Bottleneck
