-- Prove2me | Theorems.Thm_MazurCampaign_no_two_cube
-- name    : MazurCampaign.no_two_cube
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T07:18:07.798603+00:00
-- url     : https://prove2.me/theorems/2124f890-59e8-4708-a641-0e3554f25206
-- title:
--   Rational torsion excludes two cube
-- statement:
--   For every elliptic curve $E/\mathbb Q$, there is no injective additive homomorphism
--   $$ (\mathbb Z/2\mathbb Z)^3\longrightarrow E(\mathbb Q)_{\mathrm{tors}}. $$
--   Ellipticity is the only curve hypothesis. This excludes a subgroup, rather than claiming that the curve has no individual points of every order dividing that subgroup. It supplies the c2Cube input to the finite-abelian classification and the rational_torsion_subgroup_obstructions package. The source proves this exclusion for the actual Mathlib rational-point group; this is its rational-torsion specialization.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/LowTorsionObstructions.lean

import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_two_cube
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.ForbidsEmbedding (ZMod 2 × ZMod 2 × ZMod 2) (MazurCampaign.RationalTorsion E) := by sorry
