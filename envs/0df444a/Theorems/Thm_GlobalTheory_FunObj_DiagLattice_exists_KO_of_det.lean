-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_DiagLattice_exists_KO_of_det
-- name    : GlobalTheory.FunObj.DiagLattice.exists_KO_of_det
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:20.447409+00:00
-- url     : https://prove2.me/theorems/e46356ed-fa45-4c44-b334-d0d5b2270391
-- title:
--   Diag Lattice: exists KO of det
-- statement:
--   The Diag Lattice construction uses the exists KO of det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsKOOfDet.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsKOOfDet.lean#L9-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.DiagLattice

theorem GlobalTheory.FunObj.DiagLattice.exists_KO_of_det {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k)
    (h1 : ∀ i j, M i j ∈ 𝒪[k]) (h2 : valuation k M.det = 1) : ∃ g ∈ KO k ι, g.val = M := by sorry
