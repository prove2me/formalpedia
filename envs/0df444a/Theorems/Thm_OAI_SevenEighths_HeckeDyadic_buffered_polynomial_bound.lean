-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeDyadic_buffered_polynomial_bound
-- name    : OAI.SevenEighths.HeckeDyadic.buffered_polynomial_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:38:20.158999+00:00
-- url     : https://prove2.me/theorems/b03eb07f-bf66-4f59-b094-fd9815d9a676
-- title:
--   Contour bound for smoothed Hecke sums below the zero maximum
-- statement:
--   For $0<e<1/1000$ and $\varepsilon>0$ there is $C>0$ such that for every finite family of characters $\chi_j$ with nontrivial residue characters, all $T>2$, $a\in[51/100,1]$, $i\in\mathbb N$ with `zeroMaximum χ hχ (3(i+1)T)` $<a+2e$, every $j$, Boolean `inverse`, smooth $W$ supported in $[A,B]$ with $A>0$, reals $D\ge1$, $\sigma$, `freq`, $V\ge0$ with $|\mathrm{freq}|+V\le(3i+2)T$, $C_2,C_n\ge0$, $n\in\mathbb N$, with $(1+|t|)^2|\mathcal MW(a+6e-\sigma+it)|\le C_2$ and $(1+|t|)^{n+2}|\mathcal MW(x+it)|\le C_n$ for $x\in[a+6e-\sigma,2-\sigma]$: writing $K=C\,(\texttt{presentationComplexity}\,\chi_j\,((3i+2)T))^\varepsilon$,
--   $$\|\texttt{polynomial}\,\chi_j\,\mathrm{inverse}\,W\,D\,\sigma\,\mathrm{freq}\|\le\frac1{2\pi}\Big(C_2D^{a+6e-1/2}K\pi+2\frac{C_nD^{3/2}K}{(1+V)^n}|2-a-6e|+\frac{C_nD^{3/2}\,\texttt{HeckeReciprocalBound.bound}\,2}{(1+V)^n}\pi\Big).$$
--
--   Lean: `OAI.SevenEighths.HeckeDyadic.buffered_polynomial_bound` in `lean/OAI/NumberTheory/DirichletL/Hecke/DyadicBounded.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem buffered_polynomial_bound (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (D σ freq V C₂ Cn : ℝ) (n : ℕ), 1≤D → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      let K := C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε
      ‖polynomial (χ j) inverse W D σ freq‖≤(1/(2*Real.pi))*
        (C₂*D^(a+6*e-1/2)*K*Real.pi +
         2*(Cn*D^(3/2 : ℝ)*K/(1+V)^n)*|2-a-6*e| +
         (Cn*D^(3/2 : ℝ)*HeckeReciprocalBound.bound 2)/(1+V)^n*Real.pi) := by
  sorry

end SevenEighths.HeckeDyadic

end

end OAI
end
