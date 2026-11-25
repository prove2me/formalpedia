-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_expand
-- name    : GlobalTheory.CompanionTheory.ZuckCasSplit.expand
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:25:37.534949+00:00
-- url     : https://prove2.me/theorems/33ed2a88-73fe-43e7-963a-401dce410c03
-- title:
--   Zuck Cas Split: expand
-- statement:
--   The Zuck Cas Split construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L161-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L161-L169

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckCasSplit
open Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk)
variable {k r : ℕ}
set_option linter.unusedSectionVars false
variable {ι κ V : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.ZuckCasSplit.expand {R α : Type} [Ring R] [Fintype α] (E A B : α → α → R) (Q : R)
    (h1 : ∑ a, ∑ b, A a b * B b a = Q) (h2 : ∑ a, ∑ b, B a b * A b a = Q) :
    ∑ a, ∑ b, (E a b + (A a b + B a b)) * (E b a + (A b a + B b a)) =
      ∑ a, ∑ b, (E a b + A a b) * (E b a + A b a) + ∑ a, ∑ b, (E a b + B a b) * (E b a + B b a)
        - ∑ a, ∑ b, E a b * E b a + (Q + Q) := by sorry
