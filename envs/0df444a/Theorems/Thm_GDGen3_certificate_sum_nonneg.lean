-- Prove2me | Theorems.Thm_GDGen3_certificate_sum_nonneg
-- name    : GDGen3.certificate_sum_nonneg
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:41:50.411635+00:00
-- url     : https://prove2.me/theorems/8daf694c-4759-402a-9520-096588c8dabe
-- title:
--   General-N certificate lemma: certificate_sum_nonneg
-- statement:
--   The full certificate sum is nonnegative under the interpolation inequalities, for arbitrary N in the oscillatory branch.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

theorem certificate_sum_nonneg
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv (1 + r) f P i j)
    (hstar : ∀ i, i ≤ N → 0 ≤ -f i + gself (1 + r) R P i - (1 / 2) * P i i)
    (hto : ∀ i, i ≤ N → 0 ≤ f i - (1 / 2) * P i i) :
    0 ≤ certSum r N (rootXi r N) f P R := by sorry
