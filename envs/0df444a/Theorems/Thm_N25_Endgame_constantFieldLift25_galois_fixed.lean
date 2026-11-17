-- Prove2me | Theorems.Thm_N25_Endgame_constantFieldLift25_galois_fixed
-- name    : N25.Endgame.constantFieldLift25_galois_fixed
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:34.549271+00:00
-- url     : https://prove2.me/theorems/39128d52-42ae-40f8-8d6a-0d11d626ff7f
-- title:
--   A unique geometric lift is fixed by arithmetic Galois
-- statement:
--   Let $P$ be a place of the rational level-$25$ function field and let $P'$ be a geometric place above it. Assume $𝒪_{P'}∩F_ℚ=𝒪_P$ and $ord_{P'}(ιf)=ord_P(f)$ for every $f∈F_ℚ$. Assume further that $P'$ is the unique geometric place whose valuation ring contracts to $𝒪_P$. Then every $σ∈Gal(\overline{ℚ}/ℚ)$ fixes $P'$ under the arithmetic action:
--
--   $$σ·P'=P'.$$
--
--   This turns uniqueness of constant-field lifting into rationality of the geometric place.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ConstantFieldLift
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open scoped Pointwise
open N25
open N25.Endgame

theorem N25.Endgame.constantFieldLift25_galois_fixed (P : QPlace) (P' : GPlace)
    (hLift : IsConstantFieldLift25 P P')
    (huniq : ∀ Q' : GPlace, Q'.toValuationSubring.comap emb25.toRingHom =
      P.toValuationSubring → Q' = P') :
    ∀ σ : N25.Gal, arithmeticGalois FQ σ • P' = P' := by sorry
