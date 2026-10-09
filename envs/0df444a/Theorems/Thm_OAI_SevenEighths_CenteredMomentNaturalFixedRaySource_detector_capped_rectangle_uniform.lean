-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentNaturalFixedRaySource_detector_capped_rectangle_uniform
-- name    : OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.detector_capped_rectangle_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:13:34.383981+00:00
-- url     : https://prove2.me/theorems/bf3228a8-c44b-4b00-a614-22ee5574a0f1
-- title:
--   Capped rectangle bound for detector row sums
-- statement:
--   For $\varepsilon>0$, $B\ge0$ there is $J$ such that for every nonzero ideal $Q$ there is $C>0$ with: for all $Z\ge1$, every `Character` $\eta$, nonzero $m,A,z$ with `goodLambda`$\mid m$, $2\mid m$, `rowConductorBound η m 1 (A z)` $\le Z^B$ and `FixedInducingRow η Q m A z`, Booleans $r_1,r_2$, $j,k\le2$, $\sigma_1,\sigma_2\in[0,1]$, reals $t_1,t_2,h$, $L>0$, $X_1,X_2,Y_1,Y_2\ge L$ with $X_1X_2=Y_1Y_2=T$: with $D_1=$`detectorSchwartz r₁ j σ₁ t₁`, $D_2=$`detectorSchwartz r₂ k σ₂ t₂` and $\Sigma(D,X)=$`rowTwistedSum η m A z D h X`,
--   $$\big\|T^{-1/2}\big(\Sigma(D_1,X_1)\Sigma(D_2,X_2)-\Sigma(D_1,Y_1)\Sigma(D_2,Y_2)\big)\big\|\le C\,Z^{\varepsilon}(1+|t_1|+|t_2|+|h|)^J\frac{\sqrt T}{\max(1,L)}.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.detector_capped_rectangle_uniform` in `lean/OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceDetectorCapped.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CenteredMomentDetectorDictionary
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredExceptionalProfile
local notation "O" => HeckeFamily.O

theorem detector_capped_rectangle_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ∀η : Character,∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h X₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h X₂-
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h Y₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h Y₂)‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(Real.sqrt T/max 1 L) := by
  sorry

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end
