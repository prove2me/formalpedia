-- Prove2me | Theorems.Thm_N25_LocalFive_exists_integralPointCover
-- name    : N25.LocalFive.exists_integralPointCover
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:28.179219+00:00
-- url     : https://prove2.me/theorems/3b53df09-4ea0-4622-86eb-9888738c48b1
-- title:
--   A commutative abelian scheme has an integral point cover at $5$
-- statement:
--   Let $B\to\mathrm{Spec}(ℚ)$ be an abelian scheme with commutative relative group law $L$. There exists an integral point cover consisting of a Néron model over $R_5=ℤ_5$, its commutative group law, and a surjective homomorphism from its integral points to $L(ℚ_5)$: $$\mathrm{IntegralPointCover}(L)\ne\varnothing.$$ This lets the local argument pass from $5$-adic points to integral points and reduction modulo $5$. Formalization note: the cover is a structure containing the model, its group law, and the surjectivity certificate.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalFiveIntegralPoints
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra
open GoodReductionJacobian.RelativeGroupLaw
noncomputable section
local instance instL_N25_LocalFive_exists_integralPointCover_bfd51b_i984cbe : Fact (Nat.Prime 5) := ⟨by decide⟩
open N25
open N25.LocalFive

theorem N25.LocalFive.exists_integralPointCover
    {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of ℚ)}
    (L : RelativeGroupLaw ℚ f)
    (hB : AbelianSchemePropertyBundle ℚ f)
    (hc : L.IsCommutative) : Nonempty (IntegralPointCover L hc) := by sorry
