-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstAmplifiedPaidAdmission_actual_active_error_admission
-- name    : OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission.actual_active_error_admission
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:25:38.939277+00:00
-- url     : https://prove2.me/theorems/830c36a3-646e-43ea-83e5-90a8183c53b1
-- title:
--   Exponent admission for active error children
-- statement:
--   For an `Input` $s$, characters $\tau,\upsilon$, `Supported` $C,D$ with equal prime support, $R_0$, $E$, an allocation $B$ with nonzero frozen coefficient, $t$, reals $K>0$, $Z>1$, $\sigma\ge0$, $\delta$, `reserve`, `cost` $>0$, $a>0$, a nonzero element $p$ with $\log_Z\texttt{normValue}(p)\ge\sigma/6$ coprime to the active slots, $k\in\{1,6,7\}$, and the further hypotheses of the Lean: with the error input and $\delta_1=M_{\mathrm{decl}}-(\log_ZK+\log_ZN(s.\eta.\mathrm{modulus}))+$`sourceReserve …`, we have $\delta_1\ge0$, $\log_Z\texttt{volume}\,s+(6\kappa-1)\sum_i\log_ZP_i\le M_{\mathrm{decl}}$, and $\log_Z\texttt{preVolume}(\dots)-\log_Z\texttt{envelopeRef}(\mathrm{cost}\,N(\tau)Z^{\texttt{errorMoving}\,p\,Z\,k},\dots)\le\log_Z\texttt{volume}\,s-M_{\mathrm{decl}}+6\,\texttt{errorRemoval}\,p\,Z\,k+\delta_1+\log_Z\texttt{ratioPenalty}\,n$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission.actual_active_error_admission` in `lean/OAI/NumberTheory/DirichletL/Moments/FirstAmplifiedPaidAdmission.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

open CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedChildCapacity

local instance instDecidableEq_solutions_rc6dcf0_1 {κ:Type*}:DecidableEq κ:=Classical.decEq _
theorem actual_active_error_admission (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤ sigma)
    (hl:sigma/6≤Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0)
    (Cpick Rpick:Ideal O)(hside:Cpick=C₂ ∨ Cpick=D₂)
    (B₂:actualAllocations (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).pools Cpick)
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).ν (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).W (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P≠0)
    (κ Mdecl:ℝ)(hκ:1/6≤κ)(hP:∀i,1≤ s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤Mdecl):
    let input:=errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+6*errorRemoval p Z k+delta1+Real.logb Z (ratioPenalty n) := by
  sorry

end SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

end

end OAI
end
