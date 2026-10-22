-- Prove2me | Theorems.Thm_GDGen3_certificate_identity_explicit_roots
-- name    : GDGen3.certificate_identity_explicit_roots
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:31:16.47356+00:00
-- url     : https://prove2.me/theorems/59f270ec-2429-4fb8-acac-a66f25588dc0
-- title:
--   General-N certificate lemma: certificate_identity_explicit_roots
-- statement:
--   Certificate identity (20), for every N >= 1 and 0 < r < 1, using explicitly constructed positive roots; no root hypotheses are assumed.
--
--   Formalization scope: this node is part of the all-horizon algebraic certificate development. Its interpolation, Gram, trajectory, and terminal hypotheses, where present in the formal statement, are explicit inputs. This release does not claim that the full function-class supremum theorem has been assembled in Lean. See the explicit-root identity and both branch bounds for the verified algebraic results.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

theorem certificate_identity_explicit_roots
    (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (X0 : ℝ)
    (hP : ∀ i j, P i j = P j i) :
    certSum r N (rootXi r N) f P R = certRhs r N P R X0 := by sorry
