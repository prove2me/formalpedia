-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstPhysicalSource_FixedPair_right_window_energy
-- name    : OAI.SevenEighths.CenteredMomentFirstPhysicalSource.FixedPair.right_window_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:46.717977+00:00
-- url     : https://prove2.me/theorems/fe9b5c15-a7c7-455a-92c3-1aa6f5576f81
-- title:
--   Energy of right window children of a fixed pair
-- statement:
--   Let $F$ be a `FixedPair η C D hC E ξ₁ ξ₂` with `Supported` $D$ of the same prime support as $C$, $s$ `OriginalData`, $t,\theta$, $X>0$, $L$, a Schwartz $U$ and $K>0$ with $\operatorname{Re}U(\|\texttt{eisEmbedding}\,z\|^2/K)\ge0$, $J$ and $B\ge0$. If $\operatorname{Re}\texttt{commonEnergy}\,s\,D\,F.\mathrm{right}\,v\,L\,U\,K\le B(1+|v|)^{2J}$ for all $v$, then
--   $$\operatorname{Re}\sum_{z\in\mathcal O}\|\texttt{rightWindowChild}(\dots,\theta,X,\texttt{logAnnulus},z)\|^2\,U(\|\texttt{eisEmbedding}\,z\|^2/K)\le\big(\texttt{windowBudget}\,J\,t\,B\,(1+|\theta|)^J\big)^2.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentFirstPhysicalSource.FixedPair.right_window_energy` in `lean/OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSourceFixedEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.right_window_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(B:ℝ)(hB:0≤B)
    (hsource:∀v:ℝ,(commonEnergy s D hD F.right v L U K).re≤B*(1+‖v‖)^(2*J)):
    (∑'z:O,((‖rightWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L θ X logAnnulus z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K)).re≤(windowBudget J t B*(1+‖θ‖)^J)^2:= by
  sorry

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end
