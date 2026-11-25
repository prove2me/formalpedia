-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_zeta_leaf_main_term
-- name    : GlobalTheory.MainTerm.zeta_leaf_main_term
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:58:46.50526+00:00
-- url     : https://prove2.me/theorems/0d8dff95-147a-480a-b5eb-4f32a02c25ca
-- title:
--   Main Term: zeta leaf main term
-- statement:
--   The Main Term construction uses the zeta leaf main term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesLeafMainTermCurveSystem.lean#L77-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesLeafMainTermCurveSystem.lean#L77-L183

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesCoeffMulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesLeafMainTermCurveSystem
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.MainTerm
open Formalism.BaseCaseIdentities (Data Kn s0)

theorem GlobalTheory.MainTerm.zeta_leaf_main_term : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → i < d → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ κ : J, G.ty (Sum.inr κ) = a + (i : ZMod d) → WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (S.ze t κ) - ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, mainVec S D (em δ) κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i)) := by sorry
