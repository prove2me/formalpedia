-- Prove2me | Theorems.Thm_N25_canonicalChartPairPresentation25_jacobian_span_good
-- name    : N25.canonicalChartPairPresentation25_jacobian_span_good
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:14.949634+00:00
-- url     : https://prove2.me/theorems/2adc57b7-286e-4a29-8275-3ea7ff18c73e
-- title:
--   The local presentation Jacobians generate one in good characteristic
-- statement:
--   Let $p$ be a prime equal to $2$ or $3$, let $K$ be a field of characteristic $p$, and fix a pivot chart $i$. As $(j,k)$ ranges over the permitted nonpivot column pairs, let $J_{i,(j,k)}$ be the corresponding presentation Jacobian in the chart ring. Then $$\bigl(J_{i,(j,k)}:(j,k)\bigr)=(1).$$ This is the covering condition that makes the chart locally standard smooth of relative dimension one.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalChartPresentations
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25

theorem N25.canonicalChartPairPresentation25_jacobian_span_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] (pivot : Fin 4) :
    Ideal.span (Set.range fun pair : CanonicalChartColumnPair25 pivot =>
      (canonicalChartPairPresentation25 K pivot pair).jacobian) = ⊤ := by sorry
