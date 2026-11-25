-- Prove2me | Theorems.Thm_MassDataIdxEmb_gen_of_two
-- name    : MassDataIdxEmb.gen_of_two
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:56.741763+00:00
-- url     : https://prove2.me/theorems/4433022c-bc54-4420-8dcd-c135e39a9786
-- title:
--   Mass Data Idx Emb: gen of two
-- statement:
--   The Mass Data Idx Emb construction uses the gen of two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/GenOfTwo.lean#L23-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/GenOfTwo.lean#L23-L87

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

theorem MassDataIdxEmb.gen_of_two (h2 : Module.finrank F E = 2) (p : HeightOneSpectrum (𝓞 F)) (Q Q' : Ideal (𝓞 E)) [hQ : Q.IsMaximal]
    [hQ' : Q'.IsMaximal] (hne : Q ≠ Q') [Q.LiesOver p.asIdeal] [Q'.LiesOver p.asIdeal] :
    ∃ a : 𝓞 E, ∃ c0 c1 : 𝓞 F, (∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ≠ a) ∧
      a * a + algebraMap (𝓞 F) (𝓞 E) c1 * a + algebraMap (𝓞 F) (𝓞 E) c0 = 0 ∧
      minpoly (𝓞 F) a = X ^ 2 + C c1 * X + C c0 ∧ (minpoly (𝓞 F) a).natDegree = 2 ∧
      c0 ∈ p.asIdeal ∧ c1 ∉ p.asIdeal := by sorry
