-- Prove2me | Theorems.Thm_N25_cusp_complex_endpoint_left_GammaH
-- name    : N25.cusp_complex_endpoint_left_GammaH
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:21.21826+00:00
-- url     : https://prove2.me/theorems/2500b8ed-c3b0-47dc-bc6a-183a3a6d95a6
-- title:
--   Complex cusp endpoints are invariant under left multiplication by the modular group
-- statement:
--   Let $B\mapsto P_B$ be an endpoint assignment for the complex level-$25$ function field with the finite-limit characterization $x\in\mathcal O_{P_B}$ if and only if $x(B\tau)$ has a finite limit at infinity. If $\gamma\in\Gamma_H(25)$ and $B\in\mathrm{SL}_2(\mathbb Z)$, then
--
--   $$P_{\gamma B}=P_B.$$
--
--   This makes the endpoint depend only on the left $\Gamma_H(25)$-coset of the cusp matrix.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf

set_option autoImplicit false
open scoped MatrixGroups
open N25

theorem N25.cusp_complex_endpoint_left_GammaH
    (endpoint : SL(2, ℤ) → AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField 25 N25.H25)))
    (hmem : ∀ (B : SL(2, ℤ))
      (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField 25 N25.H25)),
      x ∈ (endpoint B).toValuationSubring ↔ ∃ L : ℂ, Filter.Tendsto
        (fun τ : UpperHalfPlane => ModularCurve.realizeOf (CohCarrier.GammaH 25 N25.H25)
          (x : LaurentSeries ℂ) (B • τ)) UpperHalfPlane.atImInfty (nhds L))
    (γ B : SL(2, ℤ)) (hγ : γ ∈ CohCarrier.GammaH 25 N25.H25) :
    endpoint (γ * B) = endpoint B := by sorry
