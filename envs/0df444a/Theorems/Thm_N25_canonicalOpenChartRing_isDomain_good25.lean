-- Prove2me | Theorems.Thm_N25_canonicalOpenChartRing_isDomain_good25
-- name    : N25.canonicalOpenChartRing_isDomain_good25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:36.764114+00:00
-- url     : https://prove2.me/theorems/8956ae56-7005-43e1-b29d-dd1d95e01bc2
-- title:
--   The canonical open chart is a domain in characteristics $2$ and $3$
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, and let $K$ have characteristic $p$. Then $$Domain(A_{can,K}).$$ This installs the good-characteristic function-field chart. Formalization note: primality is an explicit typeclass hypothesis.
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

theorem N25.canonicalOpenChartRing_isDomain_good25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    IsDomain (CanonicalOpenChartRing25 K) := by sorry
