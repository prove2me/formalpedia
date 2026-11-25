-- Prove2me | Theorems.Thm_MassDataIdxEmb_emb_of_two
-- name    : MassDataIdxEmb.emb_of_two
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:33.900137+00:00
-- url     : https://prove2.me/theorems/d4b06502-7e98-4341-95ca-ba60de8d38c8
-- title:
--   Mass Data Idx Emb: emb of two
-- statement:
--   The Mass Data Idx Emb construction uses the emb of two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/GenOfTwo.lean#L102-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/GenOfTwo.lean#L102-L126

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_QuadRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GenOfTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxEmb
open NumberField IsDedekindDomain Polynomial
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem MassDataIdxEmb.emb_of_two (h2 : Module.finrank F E = 2) (p : HeightOneSpectrum (𝓞 F)) (Q Q' : Ideal (𝓞 E))
    [Q.IsMaximal] [Q'.IsMaximal] (hne : Q ≠ Q') [Q.LiesOver p.asIdeal] [Q'.LiesOver p.asIdeal] :
    Nonempty (E →ₐ[F] p.adicCompletion F) := by sorry
