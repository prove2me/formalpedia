-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckePrimeDyadic_scaled_direct_bound
-- name    : OAI.SevenEighths.HeckePrimeDyadic.scaled_direct_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:48:56.21449+00:00
-- url     : https://prove2.me/theorems/471fe3ca-93a8-411b-8e7b-987578a1fd6d
-- title:
--   Direct bound for prime dyadic polynomials at scale U^r
-- statement:
--   For $0<e<1/1000$, $\kappa>0$, $\eta\ge0$ there is $C>0$ such that for every finite family of characters $\chi_j$ with nontrivial residue characters, $T>2$, $a\in[51/100,1]$, $i$ with `zeroMaximum χ hχ (3(i+1)T)` $<a+2e$, every $j$, smooth $W$ supported in $[A,B]$ with $A>0$, reals $U\ge2$ with $N(\chi_j.\mathrm{modulus})\le U$, $0\le r\le R$, $\sigma$, `freq`, $V\ge0$ with $|\mathrm{freq}|+V\le(3i+2)T$ and $(3+(3i+2)T)^2\le U^\eta$, $C_2,C_n\ge0$, $n$, with $(1+|t|)^2|\mathcal MW(a+8e-\sigma+it)|\le C_2$ and $(1+|t|)^{n+2}|\mathcal MW(x+it)|\le C_n$ for $x\in[a+8e-\sigma,2-\sigma]$:
--   $$\|\texttt{polynomial}\,\chi_j\,W\,U^r\,\sigma\,\mathrm{freq}\|\le C\,C_2U^{(a-1/2+8e)r+\kappa}+\frac{C\,C_nU^{2R+\kappa}}{(1+V)^n}.$$
--
--   Lean: `OAI.SevenEighths.HeckePrimeDyadic.scaled_direct_bound` in `lean/OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicScaled.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B016

section

namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds

theorem scaled_direct_bound (e κ η : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R σ freq V C₂ Cn : ℝ) (n : ℕ),
      2≤U → (χ j).modulus.absNorm≤U → 0≤ r → r≤R → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^2≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2+8*e)*r+κ)+C*Cn*U^(2*R+κ)/(1+V)^n := by
  sorry

end SevenEighths.HeckePrimeDyadic

end

end OAI
end
