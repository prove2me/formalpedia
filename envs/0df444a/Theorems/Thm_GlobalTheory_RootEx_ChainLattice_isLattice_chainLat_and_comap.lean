-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ChainLattice_isLattice_chainLat_and_comap
-- name    : GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:26.48661+00:00
-- url     : https://prove2.me/theorems/bbafaa2e-01c6-4e2c-a8cc-384b404820f3
-- title:
--   Chain Lattice: is Lattice chain Lat and comap
-- statement:
--   The Chain Lattice construction uses the is Lattice chain Lat and comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLatticeChainLatAndComap.lean#L38-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLatticeChainLatAndComap.lean#L38-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLatticeChainLatAndComap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ChainLattice

theorem GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : Type) [Fintype n] [DecidableEq n] (c : ℕ),
      (∀ (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ L : Submodule 𝒪[k] (n → k), Submodule.IsLattice k L →
        Submodule.IsLattice k (chainLat ϖ c L)) ∧
      ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), Submodule.IsLattice k Λ →
        Submodule.IsLattice k (Λ.comap (inX k n c)) := by sorry
