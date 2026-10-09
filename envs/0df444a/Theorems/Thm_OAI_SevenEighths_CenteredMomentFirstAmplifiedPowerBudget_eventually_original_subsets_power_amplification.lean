-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstAmplifiedPowerBudget_eventually_original_subsets_power_amplification
-- name    : OAI.SevenEighths.CenteredMomentFirstAmplifiedPowerBudget.eventually_original_subsets_power_amplification
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:21:35.011917+00:00
-- url     : https://prove2.me/theorems/00874600-f9fb-42f8-8096-f791f335be62
-- title:
--   Amplified power budget for annular Gauss sources
-- statement:
--   With $M,H,S_{\mathrm{bad}}$ and reals $\sigma,\mathrm{loss},B_R,B_s,M_{\max},b,\eta,C_{\mathrm{sec}},\xi,\mathrm{reserve}$ as in `eventually_original_amplification_common`, eventually in $Z$ the pool $P$ is nonempty and large, and, under the hypotheses of the Lean (main and error power bounds $a_{\mathrm{main}}$, $a_{\mathrm{error}}$ for the children), the annular `normalizedGaussSource s R seed (annular profile) H0` is at most
--   $$\frac{56}{|P|}\texttt{mass}(s)^2\Big(\frac{M_{\max}+2\sigma}{\sigma/6}\sum_ja_{\mathrm{main}}(j)\,(\texttt{volume}\,s)^{\alpha_j}+\sum_{p,i}16(e_i+2)\,\texttt{localErrorCost}\,p\,e_i\,(e_i+2)\sum_\chi\sum_ja_{\mathrm{error}}(p,i,\chi,j)\Big(\frac{\texttt{volume}\,s}{N((p))^{e_i+1}}\Big)^{\alpha_j}\Big),$$
--   $e_i=$`errorIndex i`.
--
--   Lean: `OAI.SevenEighths.CenteredMomentFirstAmplifiedPowerBudget.eventually_original_subsets_power_amplification` in `lean/OAI/NumberTheory/DirichletL/Moments/FirstAmplifiedPowerBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAmplifiedPowerBudget
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

open CenteredMomentFirstAnnularInput

local instance instDecidableEqSumFinOfNatNat_solutions_rb2351f_1 {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
theorem eventually_original_subsets_power_amplification {Ω : Type*} [Fintype Ω]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (A:Finset Ω) → (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (A:Finset Ω) (p : elementPool P) i χ,(τ A p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ A:Finset Ω,∀ s : Input A,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : A→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ A p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  sorry

end SevenEighths.CenteredMomentFirstAmplifiedPowerBudget

end

end OAI
end
