-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_iwahori_block_upper_levi_lower
-- name    : GlobalTheory.CompanionTheory.BlockIwahoriUML.iwahori_block_upper_levi_lower
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:31:11.536992+00:00
-- url     : https://prove2.me/theorems/7af22df9-12ac-4934-99f8-ea9b6efa73d3
-- title:
--   Block Iwahori UML: iwahori block upper levi lower
-- statement:
--   The Block Iwahori UML construction uses the iwahori block upper levi lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean#L234-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean#L234-L239

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BlockIwahoriUML
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]

theorem GlobalTheory.CompanionTheory.BlockIwahoriUML.iwahori_block_upper_levi_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (β : Fin N → ℕ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 → (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Monotone β → ∀ g ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ nm ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ l ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ np ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, (∀ i j, β i ≤ β j → (nm : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) ∧ (∀ i j, β i ≠ β j → (l : Matrix (Fin N) (Fin N) k) i j = 0) ∧ (∀ i j, β j ≤ β i → (np : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) ∧ g = np * l * nm := by sorry
