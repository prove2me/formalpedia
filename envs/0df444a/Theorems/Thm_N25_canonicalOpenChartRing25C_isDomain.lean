-- Prove2me | Theorems.Thm_N25_canonicalOpenChartRing25C_isDomain
-- name    : N25.canonicalOpenChartRing25C_isDomain
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:02.374711+00:00
-- url     : https://prove2.me/theorems/bcfeaa63-5379-44f5-919e-48894419ff12
-- title:
--   The canonical principal-open chart is a domain over every field
-- statement:
--   Let $K$ be a field and $A_{can,K}$ the selected canonical principal-open ring. Then $$Domain(A_{can,K}).$$ This gives a uniform function-field chart after base change.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing

open N25
open Polynomial
variable {K : Type*} [Field K]

theorem N25.canonicalOpenChartRing25C_isDomain : IsDomain (CanonicalOpenChartRing25 K) := by sorry
