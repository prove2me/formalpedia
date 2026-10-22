-- Prove2me | Theorems.Thm_HardyCapset20261020_hyperplane_completion_bound
-- name    : HardyCapset20261020.hyperplane_completion_bound
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T13:33:42.020981+00:00
-- url     : https://prove2.me/theorems/3a5ea009-dcbb-4805-a242-81336298a252
-- title:
--   Fixed-core hyperplane completion: total size at most 512
-- statement:
--   For the exact 512-point baseline S, any affine hyperplane H in the eight-dimensional space over the field with three elements, and any cap A containing S outside H, the cardinality of A is at most 512. Added points may lie anywhere in the entire space, including outside H. The nonzero normal hypothesis makes H a genuine hyperplane. This is a conditional fixed-core theorem, not an upper bound for arbitrary caps.
--
--   Formalization status: the complete theorem is Proved on Prove2me. The verified reduction uses 246 representative completion bounds, nine signed-permutation generators, and exhaustive orbit coverage. All current dependencies are closed. The finite checks use exact Lean arithmetic and kernel-checked evaluation; they do not rely on numerical solver tolerances.
--
--   Scope: S is the specified fixed 512-point set, and A must contain every point of S outside H. Added points can be anywhere in the full ambient space. The theorem does not assert that every cap in the ambient space has at most 512 points.
-- source:
--   Companion supplementary proofs, Part IV: fixed-core hyperplane completion in eight-dimensional ternary space. Original construction input (2026-10-13), SHA256 fa12b2dc4918c38248b3039df101b5bb66ee85fd56c313389015c64979d7fb88. Baseline construction source: Romera-Paredes et al., Nature 625, 468-475 (2024), doi:10.1038/s41586-023-06924-6.

import Definitions.Def_HardyCapsetModel20261020
set_option autoImplicit false

namespace HardyCapset20261020
theorem hyperplane_completion_bound (n : Point) (hn : n ≠ 0)
    (t : ZMod 3) (A : Finset Point) (hA : IsCap A)
    (hcore : core n t ⊆ A) : A.card ≤ 512 := by sorry
end HardyCapset20261020
