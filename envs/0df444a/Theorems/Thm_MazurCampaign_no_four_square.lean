-- Prove2me | Theorems.Thm_MazurCampaign_no_four_square
-- name    : MazurCampaign.no_four_square
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T07:18:15.578051+00:00
-- url     : https://prove2.me/theorems/893695e2-7217-4328-bf36-fdbc5a491764
-- title:
--   Rational torsion excludes four square
-- statement:
--   For every elliptic curve $E/\mathbb Q$, there is no injective additive homomorphism
--   $$ (\mathbb Z/4\mathbb Z)^2\longrightarrow E(\mathbb Q)_{\mathrm{tors}}. $$
--   Ellipticity is the only curve hypothesis. This excludes a subgroup, rather than claiming that the curve has no individual points of every order dividing that subgroup. It supplies the c4Square input to the finite-abelian classification and the rational_torsion_subgroup_obstructions package. The source proves this exclusion for the actual Mathlib rational-point group; this is its rational-torsion specialization.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/LowTorsionObstructions.lean

import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_four_square
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.ForbidsEmbedding (ZMod 4 × ZMod 4) (MazurCampaign.RationalTorsion E) := by sorry
