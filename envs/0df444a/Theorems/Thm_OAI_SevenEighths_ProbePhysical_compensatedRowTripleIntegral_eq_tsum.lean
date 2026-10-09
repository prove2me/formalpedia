-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_compensatedRowTripleIntegral_eq_tsum
-- name    : OAI.SevenEighths.ProbePhysical.compensatedRowTripleIntegral_eq_tsum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:34:30.259+00:00
-- url     : https://prove2.me/theorems/29bb4dd9-2fa1-473f-b0a4-150337937d04
-- title:
--   The compensated row triple integral as a sum over rows
-- statement:
--   For $\eta$, $S$, `CalibrationData` $C$, nonzero $p_i$, Schwartz $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$) and $X,Y,Z>0$: `compensatedRowTripleIntegral η S C W0 W1 p X Y Z` $=\sum_{u}(2\pi)^{-3}\int$`compensatedRowOnLines η S C p W0 W1 X Y Z u t`$\,d\,$`heightMeasure`, the sum over free rows.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.compensatedRowTripleIntegral_eq_tsum` in `lean/OAI/NumberTheory/DirichletL/Detector/CompensatedRows.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

local instance instCountableO_7_rfed5df_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
attribute [local instance] OAI.SevenEighths.ProbePhysical.instMeasurableSpaceFreeRow
local instance instMeasurableSingletonClassFreeRow_rfed5df_1 : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩
theorem compensatedRowTripleIntegral_eq_tsum {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedRowTripleIntegral η S C W0 W1 p X Y Z=
      ∑'u : FreeRow,((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫t,compensatedRowOnLines η S C p W0 W1 X Y Z ⟨u.val,u.property.1⟩ t ∂heightMeasure := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
