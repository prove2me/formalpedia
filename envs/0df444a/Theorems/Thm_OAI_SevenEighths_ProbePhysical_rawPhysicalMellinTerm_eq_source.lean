-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_rawPhysicalMellinTerm_eq_source
-- name    : OAI.SevenEighths.ProbePhysical.rawPhysicalMellinTerm_eq_source
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:28:19.269195+00:00
-- url     : https://prove2.me/theorems/6632cf57-81ea-4804-bc48-4d3ab98e73db
-- title:
--   Raw physical Mellin terms in source form
-- statement:
--   For $\eta$, a finite set $S$ of maximal prime ideals containing `fixedBadPrimes`, ideals $D,I,J$, a `Supported` $K$ not divisible by any $P\in S$, Schwartz $W_0,W_1$, $X>0$, $Y,Z$, a nonzero frequency $H$ and $t,w,z$: `rawPhysicalMellinTerm η (calibrationForSet S) S D I J K … X Y Z H t w z` $=$ `sourceMellinWeight W0 W1 X Y Z (t+1-z) w z`$\cdot$`fullHighCoefficient S D η (h ↦ conj(residue h)) (t+1-z) w z (rawHighEmbedding (H,((I,J),K)))`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.rawPhysicalMellinTerm_eq_source` in `lean/OAI/NumberTheory/DirichletL/Detector/RawMellinTerm.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CubicEisenstein
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem rawPhysicalMellinTerm_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D I J K : Ideal O) (hK : Supported K)
    (hKS : ∀P∈S,¬P∣K) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (H : NonzeroFrequency) (t w z : ℂ) :
    rawPhysicalMellinTerm η (calibrationForSet S hS) S D I J K hK W0 W1 X Y Z H.val t w z=
      sourceMellinWeight W0 W1 X Y Z (t+1-z) w z *
        fullHighCoefficient S D η (fun h=>star ((calibrationForSet S hS).residueMonoid h.val))
          (t+1-z) w z (rawHighEmbedding (H,((I,J),K))) := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
