-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_ip_char
-- name    : GlobalTheory.CompanionTheory.TyFin.IpIso.ip_char
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:19:55.929612+00:00
-- url     : https://prove2.me/theorems/2ce52c89-f2e7-4ab3-97f5-45be7af4d528
-- title:
--   Ip Iso: ip char
-- statement:
--   The Ip Iso construction uses the ip char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerProductCuspidalIso.lean#L90-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerProductCuspidalIso.lean#L90-L110

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

theorem GlobalTheory.CompanionTheory.TyFin.IpIso.ip_char (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β)
    (hl : Simple lam) (hm : Simple mu) :
    ip Set.univ lam.character (fun x => mu.character (glEquiv K e x)) =
      (open Classical in if CuspIso K lam mu then 1 else 0) := by sorry
