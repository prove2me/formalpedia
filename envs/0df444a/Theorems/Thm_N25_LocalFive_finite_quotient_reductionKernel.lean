-- Prove2me | Theorems.Thm_N25_LocalFive_finite_quotient_reductionKernel
-- name    : N25.LocalFive.finite_quotient_reductionKernel
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:59.895255+00:00
-- url     : https://prove2.me/theorems/2c4cdbf1-a7e0-4d2f-84c7-63d6c33232eb
-- title:
--   Integral points modulo the reduction kernel form a finite group
-- statement:
--   Let $N\to\mathrm{Spec}(R_5)$ be a quasi-compact group scheme locally of finite type, and let $L$ be a commutative relative group law on it. Let $K_{\mathrm{red}}\le L(R_5)$ be the kernel of reduction to the residue field $k_5$. Then $$|L(R_5)/K_{\mathrm{red}}|<\infty.$$ This separates the finite special-fiber quotient from the divisible formal neighborhood of the identity. Formalization note: local finite type and quasi-compactness are supplied as morphism typeclasses.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalFiveIntegralPoints
import Definitions.Def_N25_LocalFiveArithmetic
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra GoodReductionJacobian.RelativeGroupLaw
noncomputable section
local instance instL_N25_LocalFive_finite_quotient_reductionK_bfd51b_i2fa1dd : Fact (Nat.Prime 5) := ⟨by decide⟩
open N25
open N25.LocalFive

theorem N25.LocalFive.finite_quotient_reductionKernel
    {N : Scheme.{0}} {g : N ⟶ Spec (CommRingCat.of R5)}
    (L : RelativeGroupLaw R5 g) (hc : L.IsCommutative)
    [LocallyOfFiniteType g] [QuasiCompact g] :
    Finite (L.AlgPoints hc R5 ⧸ reductionKernel L hc) := by sorry
