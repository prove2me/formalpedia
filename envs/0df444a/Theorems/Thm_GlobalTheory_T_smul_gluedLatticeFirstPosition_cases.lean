-- Prove2me | Theorems.Thm_GlobalTheory_T_smul_gluedLatticeFirstPosition_cases
-- name    : GlobalTheory.T.smul_gluedLatticeFirstPosition_cases
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:46:15.188672+00:00
-- url     : https://prove2.me/theorems/61fe68ca-df89-559c-90dc-1f4581fe97ab
-- title:
--   T: smul glued Lattice First Position cases
-- statement:
--   The T construction uses the smul glued Lattice First Position cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmulGluedLatticeFirstPositionCasesStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmulGluedLatticeFirstPositionCasesStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCases
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiesOnRamOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCasesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.smul_gluedLatticeFirstPosition_cases : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (h : GL (n ⊕ Fin 1) k), (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ h • gluedS q 1 P.ker P.vec → (∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) → (∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsLattice k), h • gluedS q 1 P.ker P.vec = lastKer Λ ∨ h • gluedS q 1 P.ker P.vec = (lastPair q Λ).lat) ∨ ∃ g : GL n k, h • gluedS q 1 P.ker P.vec = embX 1 g • gluedS q 1 P.ker P.vec := by sorry
