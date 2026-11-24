-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_mem_unitGL_iff
-- name    : GlobalTheory.CompanionTheory.UnramDict.mem_unitGL_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:20:53.615977+00:00
-- url     : https://prove2.me/theorems/cba63be9-3872-46c0-91ab-61163994829c
-- title:
--   Unram Dict: mem unit GL iff
-- statement:
--   The Unram Dict construction uses the mem unit GL iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L61-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L61-L81

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnramDict

theorem GlobalTheory.CompanionTheory.UnramDict.mem_unitGL_iff {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} (g : GL (Fin n) F) :
    g ∈ unitGL (n := Fin n) F ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ intO F) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by sorry
