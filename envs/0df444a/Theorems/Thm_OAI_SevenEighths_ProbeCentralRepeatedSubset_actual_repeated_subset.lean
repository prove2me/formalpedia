-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeCentralRepeatedSubset_actual_repeated_subset
-- name    : OAI.SevenEighths.ProbeCentralRepeatedSubset.actual_repeated_subset
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:05.240919+00:00
-- url     : https://prove2.me/theorems/7f956f30-fca2-471d-82fd-473ac76f089b
-- title:
--   Central repeated-subset row values bounded by the row cost
-- statement:
--   With the same data as `actual_three_branch_slots` and any $J\subseteq\mathrm{Fin}\,N$:
--   $$\big\|\overline{r(u)}\,\texttt{HeckeOrigin.continued}(\texttt{rowCharacter}\,S\,u)\,w\big\|\prod_{j\in J}\sum_{P\in T_j}\|W_j(N(P)/Y_j)N(P)^{z-1}\texttt{centralRepeatedTerm}(\dots)\|\le C\,\texttt{rowCost}(\dots)\,N((u))^{\epsilon}\prod_{j\in J}Y_j^{-4/25}.$$
--
--   Lean: `OAI.SevenEighths.ProbeCentralRepeatedSubset.actual_repeated_subset` in `lean/OAI/NumberTheory/DirichletL/Detector/CentralRepeatedSubset.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
namespace SevenEighths.ProbeCentralRepeatedSubset
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralRepeatedProduct
local notation "O" => HeckeFamily.O

theorem actual_repeated_subset (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : ∀j P,P∈T j→Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀J : Finset (Fin N),
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j:J,(Y j.val)^(-(4/25:ℝ)) := by
  sorry
end SevenEighths.ProbeCentralRepeatedSubset

end

end OAI
end
