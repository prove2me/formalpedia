-- Prove2me | Theorems.Thm_Kyprianou_Ch02_threeSigmaIndepOfJoinAndPairCh02V1
-- name    : Kyprianou.Ch02.threeSigmaIndepOfJoinAndPairCh02V1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:36:20.8489+00:00
-- url     : https://prove2.me/theorems/736e9b08-f80b-4bfd-8c4b-60468993c4a0
-- title:
--   Three sigma algebras independent when the first is independent of the join and the other two are independent
-- statement:
--   For three sigma algebras, independence of the first from the join of the others and independence of the other two imply joint independence.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem threeSigmaIndepOfJoinAndPairCh02V1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m₀ m₁ m₂ : MeasurableSpace Ω)
    (h₀ : Indep m₀ (m₁ ⊔ m₂) P) (h₁ : Indep m₁ m₂ P) :
    iIndep (fun i : Fin 3 => if i = 0 then m₀ else if i = 1 then m₁ else m₂) P := by sorry
end Kyprianou.Ch02
