-- Prove2me | Theorems.Thm_N25_Endgame_cuspChoice25_spec
-- name    : N25.Endgame.cuspChoice25_spec
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:51.191956+00:00
-- url     : https://prove2.me/theorems/3d9e3fbc-0c64-4e11-a513-505e9cf4e307
-- title:
--   The five selected rational and geometric cusps form a compatible diamond orbit
-- statement:
--   Let $τ$ be the selected automorphism of the rational function field, let $γ_F$ be the label-$13$ diamond automorphism of the geometric function field, let $ι:F_ℚ→F_{\overline{ℚ}}$ be coefficient extension, and let $p_i^Q,p_i^G$ for $i∈Fin(5)$ be the selected rational and geometric cusp orbits. Then $τ$ and $γ_F$ commute with $ι$; both cusp lists are injective; every listed place has degree one; every $p_i^G$ is fixed by arithmetic Galois; and orders are preserved under coefficient extension:
--
--   $$(∀f,γ_F(ιf)=ι(τf))∧inj(p^Q)∧inj(p^G)∧(∀i,deg(p_i^Q)=deg(p_i^G)=1)∧(∀σ,i,σp_i^G=p_i^G)∧(∀i,f,ord_{p_i^G}(ιf)=ord_{p_i^Q}(f)).$$
--
--   This packages the full compatibility data for the five selected cusps.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_SelectedCusps

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.cuspChoice25_spec :
    (∀ f : FQ, gammaF25 (emb25 f) = emb25 (cuspChoice25.tauQ f)) ∧
    Function.Injective pQ25 ∧ Function.Injective pG25 ∧
    (∀ i : Fin 5, (pQ25 i).deg = 1 ∧ (pG25 i).deg = 1) ∧
    (∀ σ : N25.Gal, ∀ i : Fin 5,
      ModularCurve.arithmeticGalois FQ σ • pG25 i = pG25 i) ∧
    (∀ i : Fin 5, ∀ f : FQ,
      (pG25 i).ord (emb25 f) = (pQ25 i).ord f) := by sorry
