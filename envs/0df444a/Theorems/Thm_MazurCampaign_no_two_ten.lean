-- Prove2me | Theorems.Thm_MazurCampaign_no_two_ten
-- name    : MazurCampaign.no_two_ten
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T07:18:22.371084+00:00
-- url     : https://prove2.me/theorems/b647ba78-ea00-4f07-aee5-c0c44c529236
-- title:
--   Rational torsion excludes two ten
-- statement:
--   For every elliptic curve $E/\mathbb Q$, there is no injective additive homomorphism
--   $$ \mathbb Z/2\mathbb Z\times\mathbb Z/10\mathbb Z\longrightarrow E(\mathbb Q)_{\mathrm{tors}}. $$
--   Ellipticity is the only curve hypothesis. This excludes a subgroup, rather than claiming that the curve has no individual points of every order dividing that subgroup. It supplies the c2c10 input to the finite-abelian classification and the rational_torsion_subgroup_obstructions package. The source proves this exclusion for the actual Mathlib rational-point group; this is its rational-torsion specialization.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/ExceptionalProducts.lean

import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_two_ten
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.ForbidsEmbedding (ZMod 2 × ZMod 10) (MazurCampaign.RationalTorsion E) := by sorry
