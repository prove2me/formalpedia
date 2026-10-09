-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowIntegral_central_decomposition
-- name    : OAI.SevenEighths.ProbeHighRowFamily.rowIntegral_central_decomposition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:48.653665+00:00
-- url     : https://prove2.me/theorems/f0d28769-99bf-4bfa-87d5-e527c08c2455
-- title:
--   Contour decomposition of a row integral at the centre
-- statement:
--   For $0<e<1/1000$, $a\in[51/100,1]$, $B>2$, $0\le H\le(3i+2)B$, $S$ maximal with `SourceExclusions S` and `FirstTail (4e) S`, injective primes outside $S$, $\eta$, $u\ne1$, twists with the detector condition, Schwartz $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$) and $X,Y,Z>0$: with $k(\sigma,p)=$`continuedRowOnLines … σ (1-a-6e) (17/50) p` and $E=\{t:|t_{11}|\le H\}$, $k(a+16e)$ is integrable on $E$ and
--   $$\texttt{rowIntegral}(\dots,u)=(2\pi)^{-3}\Big(\int_Ek(a+16e)+i\Big(\int\!\!\int_{a+16e}^2k(v,(-H,q_1),q_2)\,dv\,dq-\int\!\!\int_{a+16e}^2k(v,(H,q_1),q_2)\,dv\,dq\Big)+\int_{E^c}k(2)\Big).$$
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.rowIntegral_central_decomposition` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/CentralIntegral.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem rowIntegral_central_decomposition {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH0 : 0≤H) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
    let E : Set HeightSpace := {t | |t.1.1|≤H}
    IntegrableOn (k (a+16*e)) E heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ((∫p : HeightSpace in E,k (a+16*e) p ∂heightMeasure)+
          I*((∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2)) ∂volume.prod volume)-
            (∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)) ∂volume.prod volume))+
          ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure) := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
