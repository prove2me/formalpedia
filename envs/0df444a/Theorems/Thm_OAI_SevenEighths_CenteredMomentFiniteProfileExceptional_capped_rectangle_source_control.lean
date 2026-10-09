-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFiniteProfileExceptional_capped_rectangle_source_control
-- name    : OAI.SevenEighths.CenteredMomentFiniteProfileExceptional.capped_rectangle_source_control
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:14:47.914634+00:00
-- url     : https://prove2.me/theorems/29a3f500-842e-4cec-8d19-5319d35c9080
-- title:
--   Capped rectangle bound for products of row-twisted sums
-- statement:
--   For reals $a>0$, $b\ge0$, $\varepsilon>0$, $B\ge0$ there are $J\in\mathbb N$ and a finite $S\ni(0,0)$ such that for every nonzero ideal $Q$ there is $C>0$ with: for all Schwartz $W_1,W_2$ supported in $[a,b]$, $Z\ge1$, every `Character` $\eta$ and nonzero $m,A_0,z$ with `goodLambda`$\mid m$, $2\mid m$, `rowConductorBound η m 1 (A₀ z)` $\le Z^B$ and `FixedInducingRow η Q m A₀ z`, and reals $t$, $L>0$, $X_1,X_2,Y_1,Y_2\ge L$ with $X_1X_2=Y_1Y_2=T$:
--   $$\big\|T^{-1/2}\big(\Sigma(W_1,X_1)\Sigma(W_2,X_2)-\Sigma(W_1,Y_1)\Sigma(W_2,Y_2)\big)\big\|\le C\,\texttt{sourceControl}\,S\,W_1\cdot\texttt{sourceControl}\,S\,W_2\cdot Z^{\varepsilon}(1+|t|)^J\frac{\sqrt T}{\max(1,L)},$$
--   with $\Sigma(W,X)=$`rowTwistedSum η m A₀ z W t X`.
--
--   Lean: `OAI.SevenEighths.CenteredMomentFiniteProfileExceptional.capped_rectangle_source_control` in `lean/OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalCapped.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight
open CenteredMomentHeckeTwist
local notation "O" => HeckeFamily.O
theorem capped_rectangle_source_control
    (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/max 1 L) := by
  sorry
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end
