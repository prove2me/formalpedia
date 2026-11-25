-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_zero_of_mem_all_powers
-- name    : GlobalTheory.T.eq_zero_of_mem_all_powers
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:52.433228+00:00
-- url     : https://prove2.me/theorems/1cb357d5-4236-5a92-b338-a1c849fe5d4d
-- title:
--   T: eq zero of mem all powers
-- statement:
--   The T construction uses the eq zero of mem all powers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/IsobaricBaseChange/IntegralCoefficientBaseChange/UnitaryBaseChangeCharacters/UnitaryBaseChangeLinks/EqZeroOfMemAllPowers.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/IsobaricBaseChange/IntegralCoefficientBaseChange/UnitaryBaseChangeCharacters/UnitaryBaseChangeLinks/EqZeroOfMemAllPowers.lean#L9-L10

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfMemAllPowers
import Mathlib
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_IsobaricBaseChange_IntegralCoefficientBaseChange_UnitaryBaseChangeCharacters_UnitaryBaseChangeLinks_EqZeroOfMemAllPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG

theorem GlobalTheory.T.eq_zero_of_mem_all_powers : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P), (∀ m, a ∈ GlobalTheory.NormEq.piPow h P m) → a = 0 := by sorry
