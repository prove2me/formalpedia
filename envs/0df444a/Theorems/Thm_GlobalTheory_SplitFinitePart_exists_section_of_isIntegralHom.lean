-- Prove2me | Theorems.Thm_GlobalTheory_SplitFinitePart_exists_section_of_isIntegralHom
-- name    : GlobalTheory.SplitFinitePart.exists_section_of_isIntegralHom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:08.751875+00:00
-- url     : https://prove2.me/theorems/2a220354-a65c-439e-8f4d-bcde307dda6f
-- title:
--   Split Finite Part: exists section of is Integral Hom
-- statement:
--   The Split Finite Part construction uses the exists section of is Integral Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L9-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSectionOfIsIntegralHom.lean#L9-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart

theorem GlobalTheory.SplitFinitePart.exists_section_of_isIntegralHom {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {N : Scheme.{0}} (g : N ⟶ Sp R) [IsIntegralHom g] (γ : Sp K ⟶ N)
    (hγ : γ ≫ g = spMap (algebraMap R K)) : ∃ s : Sp R ⟶ N, s ≫ g = 𝟙 _ ∧ spMap (algebraMap R K) ≫ s = γ := by sorry
