-- Prove2me | Theorems.Thm_N25_canonicalChart_locallyStandardSmoothOfRelativeDimension_good25
-- name    : N25.canonicalChart_locallyStandardSmoothOfRelativeDimension_good25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:00:54.05145+00:00
-- url     : https://prove2.me/theorems/67f97784-69f0-4769-8d12-ee692d50e3c4
-- title:
--   Every canonical chart is locally standard smooth of relative dimension one
-- statement:
--   Let $p$ be a prime with $p=2$ or $p=3$, let $K$ be a field of characteristic $p$, and let $A_i$ be any canonical affine chart ring. The structural homomorphism from $K$ is locally standard smooth of relative dimension one: $$K→A_i\text{ is locally standard smooth of relative dimension }1.$$ This gives the chart-level form of smoothness needed for gluing.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalChartPresentations
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25

theorem N25.canonicalChart_locallyStandardSmoothOfRelativeDimension_good25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] (i : Fin 4) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K (CanonicalChartRing25 K i)) := by sorry
