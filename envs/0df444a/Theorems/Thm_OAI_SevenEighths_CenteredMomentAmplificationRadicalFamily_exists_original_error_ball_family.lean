-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentAmplificationRadicalFamily_exists_original_error_ball_family
-- name    : OAI.SevenEighths.CenteredMomentAmplificationRadicalFamily.exists_original_error_ball_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:23:27.577545+00:00
-- url     : https://prove2.me/theorems/dd78ef8a-54b0-4a7f-b3a1-449688893a68
-- title:
--   Amplification errors on a dyad bounded by child energies
-- statement:
--   Let $\eta$ be a `Character`, $m\ne0$, $p$ a prime Eisenstein integer with $(p)$ maximal, prime and `Supported`, avoiding `goodLambda`, residue characteristic $\ne2$, `goodLambda`$^2\mid p-1$, `goodLambda`$\mid m$, $2\mid m$, and $n\in\{0,5,6\}$. Then there is a map $\tau$ from ray characters to characters with modulus norms at most `radicalBound (childCharacter η χ) m p (errorMovingExponent n)` such that for all `OriginalData` $D$ (nonzero ideals, prime and coprime to $(p)$ on the slot part), reals $t$, $T>0$, $Z>1$, $\sigma\ge0$, $D_0$, $c_{\log}$, and every dyadic index $j$:
--   $$\sum_{h\in\texttt{dyadRows}\,j,\ \texttt{eligible}\,D.R\,D.s\,h\,p}\|\texttt{amplificationError}(\dots,D.\texttt{coefficient}\,\eta\,m\,t\,T,\dots,p,n+1,h)\|^2\le D.\texttt{childEnergy}\,\tau\,p\,n\,t\,T\,\big(Z^{\log_Z(\texttt{dyadicScale}\,j)+\texttt{errorGain}\,D_0\,c_{\log}\,\sigma\,Z\,p\,(n+1)}\big).$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentAmplificationRadicalFamily.exists_original_error_ball_family` in `lean/OAI/NumberTheory/DirichletL/Moments/AmplificationRadicalFamily.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentAmplificationRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstFamily
open CenteredMomentAmplificationFamily
open CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentAmplificationEligibility
local notation "O"=>ActualEisensteinCubic.O

attribute [local instance] OAI.SevenEighths.CenteredMomentAmplificationRadicalFamily.instDecidableEqSumFinOfNatNat_definitions
theorem exists_original_error_ball_family {ι : Type*} [Fintype ι]
    (η : Character) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2∣p-1)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤ sigma → ∀ (j : ℤ),
        (∑ h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          ‖amplificationError Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            (fun I => multiplicity p (sourceGenerator D.columns I)) p (n+1) h‖^2)≤
          D.childEnergy τ p n t T
            (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1))) := by
  sorry

end SevenEighths.CenteredMomentAmplificationRadicalFamily

end

end OAI
end
