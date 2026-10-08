-- Prove2me | Theorems.Thm_MaxPressure_Throughput_extended_fluid_limit_equations
-- name    : MaxPressure.Throughput.extended_fluid_limit_equations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:02:25.784038+00:00
-- url     : https://prove2.me/theorems/899d82c4-3304-49b8-b01f-18a558a34256
-- title:
--   Lemma 5, p. 214 — maximum-pressure fluid-limit equations (52)–(55)
-- statement:
--   Assume EAA and take a fluid limit $(\bar Z,\bar T^a,\bar T)$ of a preemptive, processor-splitting maximum-pressure process, retaining the allocation-time coordinates for all extreme allocations $a\in\mathcal E$. It satisfies the fluid network equations and
--
--   $$\bar T_j(t)=\sum_{a\in\mathcal E}a_j\bar T^a(t),\quad \bar T^a\text{ is nondecreasing},\quad \sum_{a\in\mathcal E}\bar T^a(t)=t.$$
--
--   At every positive time when $a$ has strictly smaller pressure than some extreme allocation, $\bar T^a$ has derivative zero. This is (55), including existence of that derivative. These relations are the policy-specific input to Lemma 4.
--
--   **Formalization Note** The fluid network predicate also includes (18), which follows from (52)–(54) and the same fluid-limit construction. The sum uses a finite set exactly equal to the paper's extreme allocations.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 214, Lemma 5, (52)–(55); https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_Throughput_Dynamics

namespace MaxPressure.Throughput

/-- Lemma 5, p. 214: an extended maximum-pressure fluid limit satisfies
(14)–(17), (52)–(55). The derivative clause includes its existence when
the allocation is strictly dominated. -/
theorem extended_fluid_limit_equations {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (hN : N.Standing) (hEAA : EAA N)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω)
    (hmp : MPProcess N E Z Ta ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (Tab : (Fin J → ℝ) → ℝ → ℝ)
    (hlim : IsMPFluidLimit N P E Z Ta ω Zb Tb Tab) :
    IsFluidSolution N Zb Tb ∧
    (∀ t, 0 ≤ t → ∀ j, Tb t j = ∑ a ∈ E, a j * Tab a t) ∧
    (∀ a ∈ E, MonotoneOn (Tab a) (Set.Ici (0 : ℝ))) ∧
    (∀ t, 0 ≤ t → ∑ a ∈ E, Tab a t = t) ∧
    (∀ t, 0 < t → ∀ a ∈ E,
      (∃ a' ∈ E, pressure N a (Zb t) < pressure N a' (Zb t)) →
      HasDerivAt (Tab a) 0 t) := by sorry

end MaxPressure.Throughput
