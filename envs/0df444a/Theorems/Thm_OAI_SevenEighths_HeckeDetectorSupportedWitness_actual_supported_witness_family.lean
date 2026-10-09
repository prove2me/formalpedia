-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeDetectorSupportedWitness_actual_supported_witness_family
-- name    : OAI.SevenEighths.HeckeDetectorSupportedWitness.actual_supported_witness_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:23.916985+00:00
-- url     : https://prove2.me/theorems/b270a2ab-16a1-4131-9752-830575aa66a8
-- title:
--   Supported witnesses exist for a whole family of characters
-- statement:
--   Let $0<d_{\min}\le d_{\max}$, $0<\tau<d_{\min}/2$ with $4\tau<d_{\min}\eta$, $\varepsilon>0$, $0<e<1/1000$, $0<\kappa\le1$, $\eta\ge0$, $I\in\mathbb N$ and $12e\cdot24+8\kappa+2\eta\le\varepsilon/2$. Then there is $Z_0$ such that for all $Z\ge Z_0$, $d\in[d_{\min},d_{\max}]$, every family $\chi_{u,j}$ of characters (rows $u$, finitely many labels $j$) with nontrivial residue characters and modulus norms at most $Z^d$, every $a\in(51/100,1]$ and $i\le I$ with, for each row $u$, $a\le$`zeroMaximum (χ u) _ (3i·Z^τ)` and `zeroMaximum (χ u) _ (3(i+1)Z^τ)` $<a+2e$, and every $t^*\in[1,3/2]$, there is a choice, for every row $u$, of a `SupportedWitness (χ u) (Z^d) a ε t* (Z^τ) ((Z^d)^(τ/(2 d_max))) i`.
--
--   Lean: `OAI.SevenEighths.HeckeDetectorSupportedWitness.actual_supported_witness_family` in `lean/OAI/NumberTheory/DirichletL/Hecke/DetectorSupportedWitness.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorSupportedWitness
open HeckeFamily HeckeDetectorWitnessRows

theorem actual_supported_witness_family (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  sorry

end SevenEighths.HeckeDetectorSupportedWitness

end

end OAI
end
