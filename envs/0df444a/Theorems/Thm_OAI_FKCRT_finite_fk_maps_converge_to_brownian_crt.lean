-- Prove2me | Theorems.Thm_OAI_FKCRT_finite_fk_maps_converge_to_brownian_crt
-- name    : OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:40.087723+00:00
-- url     : https://prove2.me/theorems/81ba7106-90d1-4200-b707-a7f51f66bda5
-- statement:
--   The theorem states that, for every real q>4, there is a constant c>0 such that the following holds for every probability space (Ω,P) carrying three independent real-valued standard Brownian motions B₀,B₁,B₂ (each satisfying Mathlib's IsBrownianReal, jointly independent as random functions on the nonnegative reals). Let the standard excursion be e(t)=√(Σᵢ(Bᵢ(t)−t·Bᵢ(1))²) on [0,1], the norm of three independent Brownian bridges, and let its tree be the quotient of [0,1] by the pseudometric e(s)+e(t)−2·inf of e over the interval between s and t, carrying the pushforward of Lebesgue measure. For n≥0, the finite model is the Fortuin–Kasteleyn law on rooted oriented genus-zero planar maps with n+1 edges, loops and multiple edges allowed, together with an arbitrary subset A of edges. Its weight is q^(k(A)+(|A|−V)/2), where k(A) counts connected components of the spanning graph on all vertices with edges A and V is the number of vertices, normalized by the total partition function. Each map is viewed as its vertex set with graph distance multiplied by c/√(n+1) and with the degree measure, namely each vertex weighted by its degree divided by 2(n+1). Then for every bounded test function F on measured metric spaces that is continuous in the Gromov–Hausdorff–Prokhorov distance at all compact metric probability spaces, the expectation of F under the finite law converges, as n→∞ through all integers, to the expectation of F at the Brownian excursion tree. This is an admitted theorem statement, not a verified proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FKCRT.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FKCRT.lean; bytes 9551..9709
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_FKCRT

namespace OAI

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal NNReal

namespace FKCRT

/-- Finite FK maps converge in GHP distribution to the standard Brownian CRT. -/
theorem finite_fk_maps_converge_to_brownian_crt : MainStatement := by
  sorry

end FKCRT
end
end OAI
