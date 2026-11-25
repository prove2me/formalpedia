-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_glEquiv_conj
-- name    : GlobalTheory.CompanionTheory.TyFin.IpIso.glEquiv_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:45.172635+00:00
-- url     : https://prove2.me/theorems/9f2657f5-0852-45cb-bf12-34e9145b47c5
-- title:
--   Ip Iso: gl Equiv conj
-- statement:
--   The Ip Iso construction uses the gl Equiv conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerProductCuspidalIso.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerProductCuspidalIso.lean#L25-L33

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.IpIso
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem GlobalTheory.CompanionTheory.TyFin.IpIso.glEquiv_conj (e e' : α ≃ β) (g : GL α K) :
    glEquiv K e' g =
      pm K (e.symm.trans e') * glEquiv K e g * (pm K (e.symm.trans e'))⁻¹ := by sorry
