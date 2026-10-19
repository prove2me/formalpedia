-- Prove2me | Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyCoefficientMap_restriction_coefficientMap
-- name    : MazurTransfer.ContinuousFirstCohomologyCoefficientMap.restriction_coefficientMap
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T00:28:28.636826+00:00
-- url     : https://prove2.me/theorems/e9035083-f8ca-4ad2-85f7-bb3af5df71ac
-- title:
--   Continuous first-cohomology coefficient maps commute with subgroup restriction
-- statement:
--   Let G have a group structure and a topology, and act by automorphisms on abelian topological groups M and N. If f from M to N is continuous and equivariant, then its induced map on presented continuous H1 commutes with restriction to every subgroup S with the induced topology: $$\operatorname{res}_S(f_*x)=f_*(\operatorname{res}_Sx).$$ This is used to pass arithmetic norm-character Kummer images through local Selmer conditions. The original hypotheses on G, the actions and S are retained.
-- source:
--   Original MazurTheorem ContinuousFirstCohomologyCoefficientMap.restriction_coefficientMap, complete original type and proof body retained, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous equivariant coefficient homomorphisms induce
maps on the EXISTING continuous-cocycle H1 presentation and commute with
restriction to every subgroup. Named downstream consumer: the actual
arithmetic norm-character Kummer images and local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyCoefficientMapData
noncomputable section
open MazurTransfer.ContinuousFirstCohomologyPresentation
open MazurTransfer.ContinuousFirstCohomologySubgroupRestriction
open MazurTransfer.ContinuousFirstCohomologyCoefficientMap

theorem MazurTransfer.ContinuousFirstCohomologyCoefficientMap.restriction_coefficientMap (G M N : Type) [Group G] [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
  [IsTopologicalGroup M] [IsTopologicalGroup N]
  (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (hc : Continuous f) (S : Subgroup G) (x : H1 G M) :
    restriction G N S (coefficientMap G M N f hf hc x) =
      coefficientMap S M N f (fun s m => hf s.val m) hc (restriction G M S x) := by sorry
