-- Prove2me | Theorems.Thm_MazurCampaign_rational_torsion_subgroup_obstructions
-- name    : MazurCampaign.rational_torsion_subgroup_obstructions
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T07:18:23.157856+00:00
-- url     : https://prove2.me/theorems/092ff4dc-003f-4a81-8cfb-4a13c426489f
-- title:
--   Seven subgroup exclusions for rational elliptic torsion
-- statement:
--   For every elliptic curve $E/\mathbb Q$, none of the following seven groups embeds into its full rational torsion subgroup:
--   $$ (\mathbb Z/2\mathbb Z)^3,\quad (\mathbb Z/3\mathbb Z)^2,\quad (\mathbb Z/4\mathbb Z)^2,\quad (\mathbb Z/5\mathbb Z)^2,\quad (\mathbb Z/7\mathbb Z)^2, $$
--   $$ \mathbb Z/2\mathbb Z\times\mathbb Z/10\mathbb Z,\qquad \mathbb Z/2\mathbb Z\times\mathbb Z/12\mathbb Z. $$
--   No finiteness or point-order classification is assumed. This gathers the independent subgroup obstructions required by the finite-abelian classification; it does not itself classify torsion orders. The named downstream consumer is MazurCampaign.rationalTorsion_hasMazurClassification.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/LowTorsionObstructions.lean ; https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/OddPrimeObstructions.lean ; https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/ExceptionalProducts.lean

import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.rational_torsion_subgroup_obstructions
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.AvoidsMazurForbiddenSubgroups (MazurCampaign.RationalTorsion E) := by sorry
