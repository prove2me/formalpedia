-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finitePacketShearMatrix_entry_structure
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_entry_structure
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:08:45.783+00:00
-- url     : https://prove2.me/theorems/52e435d8-3fab-4046-80e0-fa470ae61fba
-- title:
--   Entry structure of finite packet shear matrices
-- statement:
--   Every diagonal entry of the finite packet shear matrix is one. If an off-diagonal entry is nonzero, the row exponent has strictly smaller total degree in variables X₁,…,Xₘ than the column exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_entry_structure
    {m : ℕ} (K : ℕ) (S : Finset (Fin (m + 1) → ℕ))
    (delta : Fin m → PowerSeries ℂ) :
    (∀ i : Fin K × ↥S,
      finitePacketShearMatrix K S delta i i = 1) ∧
    (∀ i j : Fin K × ↥S, i ≠ j →
      finitePacketShearMatrix K S delta i j ≠ 0 →
      (∑ k : Fin m, (InterpolationMatrix.exponentVector i.2.val) k.succ) <
      (∑ k : Fin m, (InterpolationMatrix.exponentVector j.2.val) k.succ)) := by sorry
