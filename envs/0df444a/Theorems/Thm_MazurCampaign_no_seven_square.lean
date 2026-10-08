-- Prove2me | Theorems.Thm_MazurCampaign_no_seven_square
-- name    : MazurCampaign.no_seven_square
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T07:18:25.397964+00:00
-- url     : https://prove2.me/theorems/b478107a-960f-4204-bd46-12a51a751ac3
-- title:
--   Rational torsion excludes seven square
-- statement:
--   For every elliptic curve $E/\mathbb Q$, there is no injective additive homomorphism
--   $$ (\mathbb Z/7\mathbb Z)^2\longrightarrow E(\mathbb Q)_{\mathrm{tors}}. $$
--   Ellipticity is the only curve hypothesis. This excludes a subgroup, rather than claiming that the curve has no individual points of every order dividing that subgroup. It supplies the c7Square input to the finite-abelian classification and the rational_torsion_subgroup_obstructions package. The source proves this exclusion for the actual Mathlib rational-point group; this is its rational-torsion specialization.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/OddPrimeObstructions.lean

import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_seven_square
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.ForbidsEmbedding (ZMod 7 × ZMod 7) (MazurCampaign.RationalTorsion E) := by sorry
