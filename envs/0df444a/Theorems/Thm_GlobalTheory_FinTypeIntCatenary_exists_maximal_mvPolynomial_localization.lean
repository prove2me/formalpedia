-- Prove2me | Theorems.Thm_GlobalTheory_FinTypeIntCatenary_exists_maximal_mvPolynomial_localization
-- name    : GlobalTheory.FinTypeIntCatenary.exists_maximal_mvPolynomial_localization
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:43.766977+00:00
-- url     : https://prove2.me/theorems/1d86985c-e0af-4b7e-9195-59a8449e32ad
-- title:
--   Fin Type Int Catenary: exists maximal mv Polynomial localization
-- statement:
--   The Fin Type Int Catenary construction uses the exists maximal mv Polynomial localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L100-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L100-L158

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeightMaximalLePrimeAddDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinTypeIntCatenary
open ReciprocityTheory.CA

theorem GlobalTheory.FinTypeIntCatenary.exists_maximal_mvPolynomial_localization (N : ℕ) (p : Ideal ℤ) [p.IsMaximal] (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal]
    (hc : 𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ) = p) :
    ∃ (𝔑' : Ideal (MvPolynomial (Fin N) (Localization.AtPrime p))) (_ : 𝔑'.IsMaximal),
      𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Nonempty (Localization.AtPrime 𝔑' ≃+* Localization.AtPrime 𝔑) ∧ 𝔑'.height = 𝔑.height := by sorry
