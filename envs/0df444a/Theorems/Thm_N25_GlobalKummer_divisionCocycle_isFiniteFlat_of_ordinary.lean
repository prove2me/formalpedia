-- Prove2me | Theorems.Thm_N25_GlobalKummer_divisionCocycle_isFiniteFlat_of_ordinary
-- name    : N25.GlobalKummer.divisionCocycle_isFiniteFlat_of_ordinary
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:37.976511+00:00
-- url     : https://prove2.me/theorems/f25a88a3-a1ba-472b-a5b7-862fbc77ac7e
-- title:
--   The local division cocycle at $71$ is finite flat
-- statement:
--   Let $J$, $M$, $π$, and $V=\ker π$ be as above, and assume the cyclotomic relation and the ordinary finite-flat Kummer condition at $71$. For $P\in M$ and $Q\in J$ satisfying $π(Q)=P$, restrict the cocycle $c_{P,Q}(σ)=σQ-Q$ to $G_{ℚ_{71}}$. Then its associated extension of the restricted kernel representation is finite flat: $$c_{P,Q}|_{G_{ℚ_{71}}}\ \text{is a finite-flat cocycle for }V|_{G_{ℚ_{71}}}.$$ This supplies the local condition at the prime equal to the torsion exponent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalFiniteFlatClasses
import Definitions.Def_N25_OrdinaryKummerFiniteFlat
import Definitions.Def_N25_LocalKummerOperators
import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false
noncomputable section
open CategoryTheory groupCohomology
open N25
open N25.GlobalKummer
local instance ordinaryDivisionPrime_ibfc5bf : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.GlobalKummer.divisionCocycle_isFiniteFlat_of_ordinary
    (hPhi : PhiFiveZero) (hN71 : OrdinaryKummerFiniteFlat)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J)) :
    IsFiniteFlatCocycle 71 (localKernelRep hPhi).ρ
      (fun σ => divisionCocycle hPhi P Q hQ (localGaloisToGlobal 71 σ)) := by sorry
