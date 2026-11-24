-- Prove2me | Theorems.Thm_GlobalTheory_T_not_isRoot_residue_cofactor_unramifiedExt
-- name    : GlobalTheory.T.not_isRoot_residue_cofactor_unramifiedExt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:54:01.012044+00:00
-- url     : https://prove2.me/theorems/0d80ccc2-d7aa-42e9-aeb6-585027bc3f77
-- title:
--   T: not is Root residue cofactor unramified Ext
-- statement:
--   The T construction uses the not is Root residue cofactor unramified Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotIsRootResidueCofactorUnramifiedExtStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotIsRootResidueCofactorUnramifiedExtStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsRootResidueCofactorUnramifiedExt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsRootResidueCofactorUnramifiedExtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.not_isRoot_residue_cofactor_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O, (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z) → ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic → r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree → p.natDegree = d * r.natDegree → p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) → ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := by sorry
