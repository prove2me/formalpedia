-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstMixedWindow_original_four_budget_reference
-- name    : OAI.SevenEighths.CenteredMomentFirstMixedWindow.original_four_budget_reference
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:27:13.659154+00:00
-- url     : https://prove2.me/theorems/de67637a-f77a-4197-8782-2cdf900f9a71
-- title:
--   Four-window budget at the reference scale
-- statement:
--   For an `Input` $s$, ideals $R$, `seed`, tests vanishing below $a_1,a_2>0$, $m,A$, $t$, $S$, `Supported` $C,D$ with equal prime support, $E$, ray characters $\xi_1,\xi_2$, a `FixedPair` $F$, rows, Schwartz $W$, windows $U_i$ vanishing outside $[-M,M]$, reals $K,A_0,B_0>0$, $Z>1$, nonnegative $E_L,E_R$, $J_L,J_R$, `height`, and a nonzero `block`: with $V=$`volume s`,
--   $$\frac{\|\texttt{scalar}\|}{V}\sum_{i,j}\texttt{windowBudget}\,J_L\,\mathrm{height}\big(N(F.\mathrm{left})(V/N(C))^2Z^{\texttt{allowance}\,C\,D\,Z}E_L(i)\big)\texttt{windowBudget}\,J_R\,\mathrm{height}(\dots E_R(j))\le\Big(\|\texttt{inactiveWeight}\|\frac{e^M}{\prod s.lo_i\,a_1a_2}\texttt{fixedPresentationCost}\,K\frac{N(s.\eta.\mathrm{modulus})}{N(\texttt{commonRadical})}\Big)\sum_{i,j}\texttt{windowBudget}\,J_L\,\mathrm{height}\,E_L(i)\,\texttt{windowBudget}\,J_R\,\mathrm{height}\,E_R(j).$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentFirstMixedWindow.original_four_budget_reference` in `lean/OAI/NumberTheory/DirichletL/Moments/FirstMixedWindow.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMixedWindow
open CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale
local notation "O"=>HeckeFamily.O

theorem original_four_budget_reference {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z:ℝ)(EL ER:Fin 4→ℝ)(JL JR:ℕ)(height:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hEL:∀i,0≤EL i)(hER:∀i,0≤ER i)(hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (∑i:Fin 4,∑j:Fin 4,
        windowBudget JL height ((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i)*
        windowBudget JR height ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER j))≤
      (‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
        (∑i:Fin 4,∑j:Fin 4,windowBudget JL height (EL i)*windowBudget JR height (ER j)) := by
  sorry

end SevenEighths.CenteredMomentFirstMixedWindow

end

end OAI
end
