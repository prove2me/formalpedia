-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyFirstHighGaussianUniformPowers_actual_high_homogeneous_four_powers
-- name    : OAI.SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers.actual_high_homogeneous_four_powers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:12.260701+00:00
-- url     : https://prove2.me/theorems/5b5b9dbe-7ecc-4429-9b33-73555305ff7e
-- title:
--   Sum of four normalized high powers
-- statement:
--   Let $M\ne0$, $H$, $S_{\mathrm{bad}}\supseteq$`fixedBadPrimes`, characters $\eta,\tau$, `Supported` $C,D$ with equal prime support, $E$, and reals $K,V>0$, $Z>1$, $\sigma>0$, $\varepsilon\ge0$, $0\le M_{\mathrm{decl}}\le M_{\mathrm{cap}}$ with $\log_ZK+\log_ZN(\eta.\mathrm{modulus})\le M_{\mathrm{width}}\le M_{\mathrm{decl}}$, and the further data of the Lean. Then, with the main and error coefficients $a_{\mathrm{main}},a_{\mathrm{error}}$ defined there,
--   $$\sum_{j<4}\texttt{normalizedPower}\,\mathrm{upper}\,V\,N(C)\,N(\tau)\,Z\,(\texttt{allowance}\,C\,D\,Z)\,\varepsilon\,(\texttt{sourceCoefficients}\dots j)\,N\,(\alpha_j)\le\frac{\mathrm{upper}^N\cdot56\big(\tfrac{M_{\mathrm{amp}}+2\sigma}{\sigma/6}+1872|\mathrm{Ray}|\big)F}{\mathrm{seed}}Z^{M_{\mathrm{decl}}-M_0+\varepsilon B_{\mathrm{common}}+\mathrm{primeLoss}}\sum_{j<4}Z^{\mathrm{srcLoss}_j+\texttt{lossVector}\dots j}.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers.actual_high_homogeneous_four_powers` in `lean/OAI/NumberTheory/DirichletL/Energy/FirstHighGaussianUniformPowers.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

namespace SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

theorem actual_high_homogeneous_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:1≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)
    (F seed Bcommon:ℝ)(srcLoss:Fin 4→ℝ)(hF:0≤F)(hseed:0<seed)(heps1:eps≤1)
    (hncap:(C.absNorm:ℝ)≤Z^Bcommon)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (upper^N*(56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ)))*F/seed)*
        Z^(Mdecl-M0+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+lossVector sigma delta reserve paid eps Mcap saving j) := by
  sorry

end SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers

end

end OAI
end
