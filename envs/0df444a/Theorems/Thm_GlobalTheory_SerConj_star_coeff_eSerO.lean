-- Prove2me | Theorems.Thm_GlobalTheory_SerConj_star_coeff_eSerO
-- name    : GlobalTheory.SerConj.star_coeff_eSerO
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:47.511148+00:00
-- url     : https://prove2.me/theorems/2546cb0e-f077-4689-b16f-bbf6c2540801
-- title:
--   Ser Conj: star coeff e Ser O
-- statement:
--   The Ser Conj construction uses the star coeff e Ser O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L198-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L198-L233

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES

theorem GlobalTheory.SerConj.star_coeff_eSerO : ∀ {g : ℕ} [Fact g.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O →
    ∀ (r : ℕ) (f : Polynomial (ZMod g)), f.Monic → f.coeff 0 ≠ 0 → ∀ x,
      star ((Formalism.L2.NT.eSerO O r f).coeff x) =
        (Formalism.L2.NT.eSerO O r (Polynomial.C (f.coeff 0)⁻¹ * f.reverse)).coeff x := by sorry
