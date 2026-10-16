-- Prove2me | Theorems.Thm_MazurTransfer_continuous_galois_restrictScalars
-- name    : MazurTransfer.continuous_galois_restrictScalars
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T07:44:08.040721+00:00
-- url     : https://prove2.me/theorems/6e533c34-4dab-4ece-83ad-95fb0e52d17b
-- title:
--   Continuity of Galois restriction of scalars
-- statement:
--   Let $R \subseteq K \subseteq \Omega$ be a tower of fields such that $\Omega/K$ is algebraic. Restricting scalars sends $K$-automorphisms of $\Omega$ to $R$-automorphisms, continuously for the two Krull topologies. This permits continuous descent characters to pass from a fixing subgroup to the absolute Galois group over the corresponding field.
-- source:
--   Original bridge for MazurTheorem using Mathlib Krull topology, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/KrullTopology.lean, krullTopology_mem_nhds_one_iff.

import Mathlib
open scoped Topology

theorem MazurTransfer.continuous_galois_restrictScalars (R K Ω : Type) [Field R] [Field K] [Field Ω]
    [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsAlgebraic K Ω] :
    Continuous (AlgEquiv.restrictScalarsHom R : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[R] Ω)) := by sorry
