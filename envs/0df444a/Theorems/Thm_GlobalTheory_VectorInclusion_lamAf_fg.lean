-- Prove2me | Theorems.Thm_GlobalTheory_VectorInclusion_lamAf_fg
-- name    : GlobalTheory.VectorInclusion.lamAf_fg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:39:23.460218+00:00
-- url     : https://prove2.me/theorems/122333ec-3ee4-4032-b249-b11884de48c9
-- title:
--   Vector Inclusion: lam Af fg
-- statement:
--   The Vector Inclusion construction uses the lam Af fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InclEIntMem.lean#L43-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InclEIntMem.lean#L43-L71

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InclEIntMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
noncomputable section
open Classical
open GlobalTheory GlobalTheory.VectorInclusion
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.VectorInclusion.lamAf_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) := by sorry
