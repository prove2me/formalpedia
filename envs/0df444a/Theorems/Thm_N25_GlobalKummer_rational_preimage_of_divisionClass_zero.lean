-- Prove2me | Theorems.Thm_N25_GlobalKummer_rational_preimage_of_divisionClass_zero
-- name    : N25.GlobalKummer.rational_preimage_of_divisionClass_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:12.529788+00:00
-- url     : https://prove2.me/theorems/92af374d-77a1-4aee-988f-64e8f8473fca
-- title:
--   A trivial division class yields a rational preimage
-- statement:
--   Assume the cyclotomic relation. Let $P\in M=J^{G_{ℚ}}$, choose $Q\in J$ with $π(Q)=P$, and let $c_{P,Q}(σ)=σQ-Q\in V$. If the cohomology class of this cocycle is zero, then there exists a rational fixed point $R\in M$ whose image under the restriction $π_M:M\to M$ is $P$: $$[c_{P,Q}]=0\quad\Longrightarrow\quad \exists R\in M,\ π_M(R)=P.$$ This is the final descent from a geometric division point to a rational one.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummer

set_option autoImplicit false
open N25
open N25.GlobalKummer

theorem N25.GlobalKummer.rational_preimage_of_divisionClass_zero
    (hPhi : PhiFiveZero) (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J))
    (hc : groupCohomology.H1π (vRep hPhi) (divisionCocycle hPhi P Q hQ) = 0) :
    ∃ R : ↥M, piM R = P := by sorry
