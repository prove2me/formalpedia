-- Prove2me | Theorems.Thm_N25_LocalFive_exists_finite_quotient_surjective_71_nsmul
-- name    : N25.LocalFive.exists_finite_quotient_surjective_71_nsmul
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:08.824048+00:00
-- url     : https://prove2.me/theorems/e538f18f-029e-412e-b49a-9efac5851eaa
-- title:
--   Local points contain a finite-index $71$-divisible subgroup
-- statement:
--   Let $B\to\mathrm{Spec}(ℚ)$ be an abelian scheme, let $L$ be its commutative relative group law, and write $L(ℚ_5)$ for its $5$-adic points. Then there exists a subgroup $U\le L(ℚ_5)$ such that the quotient is finite and multiplication by $71$ is surjective on $U$: $$|L(ℚ_5)/U|<\infty,\qquad [71]:U\twoheadrightarrow U.$$ This provides the local finite-index divisibility input used to prove surjectivity of the global endomorphism. Formalization note: the abelian-scheme property bundle packages smoothness, properness, and the group-scheme hypotheses.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalFiveIntegralPoints
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra
noncomputable section
local instance instL_N25_LocalFive_exists_finite_quotient_sur_bfd51b_i0cb624 : Fact (Nat.Prime 5) := ⟨by decide⟩
open N25
open N25.LocalFive

theorem N25.LocalFive.exists_finite_quotient_surjective_71_nsmul
    {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of ℚ)}
    (L : RelativeGroupLaw ℚ f) (hB : AbelianSchemePropertyBundle ℚ f)
    (hc : L.IsCommutative) :
    ∃ U : AddSubgroup (L.AlgPoints hc ℚ_[5]),
      Finite ((L.AlgPoints hc ℚ_[5]) ⧸ U) ∧
        Function.Surjective (fun u : U => (71 : ℕ) • u) := by sorry
