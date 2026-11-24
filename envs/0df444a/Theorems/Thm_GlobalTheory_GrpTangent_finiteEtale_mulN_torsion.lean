-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_finiteEtale_mulN_torsion
-- name    : GlobalTheory.GrpTangent.finiteEtale_mulN_torsion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:20.017251+00:00
-- url     : https://prove2.me/theorems/24570207-97c7-4752-81fc-c64eff9f89cd
-- title:
--   Grp Tangent: finite Etale mul N torsion
-- statement:
--   The Grp Tangent construction uses the finite Etale mul N torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L659-L665
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L659-L665

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem GlobalTheory.GrpTangent.finiteEtale_mulN_torsion [hG : IsAbelianScheme G] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    (IsFinite (mulN G n).left ∧ Etale (mulN G n).left) ∧
      IsFinite (torsion G n).hom ∧ Etale (torsion G n).hom := by sorry
