-- Prove2me | Theorems.Thm_GlobalTheory_Mem_LevDual_sigR_inclE
-- name    : GlobalTheory.Mem.LevDual.sigR_inclE
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:38:04.173909+00:00
-- url     : https://prove2.me/theorems/b2ee18b6-2048-5b59-a93c-b70caab64962
-- title:
--   Lev Dual: sig R incl E
-- statement:
--   The Lev Dual construction uses the sig R incl E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryCarryDual.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryCarryDual.lean#L76-L79

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryCarryDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.LevDual

theorem GlobalTheory.Mem.LevDual.sigR_inclE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (e : E) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) =
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (σ e) := by sorry
