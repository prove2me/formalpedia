-- Prove2me | Theorems.Thm_MazurCampaign_no_three_square
-- name    : MazurCampaign.no_three_square
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T07:18:14.461562+00:00
-- url     : https://prove2.me/theorems/d5670e66-9c94-43cd-b9e9-2e8b44783b71
-- title:
--   Rational torsion excludes three square
-- statement:
--   For every elliptic curve $E/\mathbb Q$, there is no injective additive homomorphism
--   $$ (\mathbb Z/3\mathbb Z)^2\longrightarrow E(\mathbb Q)_{\mathrm{tors}}. $$
--   Ellipticity is the only curve hypothesis. This excludes a subgroup, rather than claiming that the curve has no individual points of every order dividing that subgroup. It supplies the c3Square input to the finite-abelian classification and the rational_torsion_subgroup_obstructions package. The source proves this exclusion for the actual Mathlib rational-point group; this is its rational-torsion specialization.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/LowTorsionObstructions.lean

import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_three_square
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.ForbidsEmbedding (ZMod 3 × ZMod 3) (MazurCampaign.RationalTorsion E) := by sorry
