-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_rowIntegral_summable
-- name    : OAI.SevenEighths.ProbePhysical.rowIntegral_summable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:51.225164+00:00
-- url     : https://prove2.me/theorems/5122953c-34a2-4a07-a2a2-0eb9c84d11bd
-- title:
--   Row integrals are summable
-- statement:
--   For $\eta$, $S$, `CalibrationData` $C$, nonzero $p_i$, Schwartz $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$) and $X,Y,Z>0$, the function `rowIntegral η S C p W0 W1 X Y Z` (over free rows) is summable.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.rowIntegral_summable` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalSplit.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

local instance instCountableO_8_r501281_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
attribute [local instance] OAI.SevenEighths.ProbePhysical.instMeasurableSpaceFreeRow_1
local instance instMeasurableSingletonClassFreeRow_1_r501281_1 : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩
lemma rowIntegral_summable {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (hp : ∀i,p i≠0) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Summable (rowIntegral η S C p W0 W1 X Y Z) := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
