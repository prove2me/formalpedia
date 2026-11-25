-- Prove2me | Theorems.Thm_GlobalTheory_finite_lattices_between_of_smul_le
-- name    : GlobalTheory.finite_lattices_between_of_smul_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:04:12.827798+00:00
-- url     : https://prove2.me/theorems/8b3a546f-aba4-4c48-98f1-5a530195e70e
-- title:
--   Global Theory: finite lattices between of smul le
-- statement:
--   The Global Theory construction uses the finite lattices between of smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FiniteLatticesBetweenOfSmulLe.lean#L9-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FiniteLatticesBetweenOfSmulLe.lean#L9-L50

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FiniteLatticesBetweenOfSmulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.finite_lattices_between_of_smul_le :
    ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N →
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by sorry
