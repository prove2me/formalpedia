-- Prove2me | Theorems.Thm_GlobalTheory_FontCmp_exists_liftAdd
-- name    : GlobalTheory.FontCmp.exists_liftAdd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:28:48.509999+00:00
-- url     : https://prove2.me/theorems/8e0a7f25-16be-4d88-a12e-0a80a8d46aa4
-- title:
--   Font Cmp: exists lift Add
-- statement:
--   The Font Cmp construction uses the exists lift Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FontaineFormalismTensorEquiv.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FontaineFormalismTensorEquiv.lean#L11-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FontCmp
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

theorem GlobalTheory.FontCmp.exists_liftAdd {R M N Z : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [AddCommGroup Z] (f : M → N → Z)
    (h1 : ∀ m m' n, f (m + m') n = f m n + f m' n) (h2 : ∀ m n n', f m (n + n') = f m n + f m n')
    (h3 : ∀ (r : R) m n, f (r • m) n = f m (r • n)) :
    ∃ F : M ⊗[R] N →+ Z, ∀ m n, F (m ⊗ₜ n) = f m n := by sorry
