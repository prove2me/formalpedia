-- Prove2me | Theorems.Thm_N25_LocalFive_surjective_nsmul_reductionKernel
-- name    : N25.LocalFive.surjective_nsmul_reductionKernel
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:26.041047+00:00
-- url     : https://prove2.me/theorems/7226c0db-9a5f-4ba6-afae-b58bfcb60dfa
-- title:
--   A unit scalar acts surjectively on the smooth reduction kernel
-- statement:
--   Let $N\to\mathrm{Spec}(R_5)$ be smooth, let $L$ be a commutative relative group law, and let $K_{\mathrm{red}}\le L(R_5)$ be the kernel of reduction. If $n\ge0$ is a unit in $R_5$, then $$[n]:K_{\mathrm{red}}\twoheadrightarrow K_{\mathrm{red}}.$$ This supplies the $71$-divisibility of the formal neighborhood of the identity.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalFiveIntegralPoints
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra GoodReductionJacobian.RelativeGroupLaw
noncomputable section
local instance instL_N25_LocalFive_surjective_nsmul_reduction_bfd51b_i8a6835 : Fact (Nat.Prime 5) := ⟨by decide⟩
open N25
open N25.LocalFive

theorem N25.LocalFive.surjective_nsmul_reductionKernel
    {N : Scheme.{0}} {g : N ⟶ Spec (CommRingCat.of R5)}
    (L : RelativeGroupLaw R5 g) (hc : L.IsCommutative)
    (hsm : Smooth g) (n : ℕ) (hn : IsUnit (n : R5)) :
    Function.Surjective (fun u : reductionKernel L hc => n • u) := by sorry
