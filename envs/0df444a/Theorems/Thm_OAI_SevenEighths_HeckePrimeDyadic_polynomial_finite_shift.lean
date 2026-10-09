-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckePrimeDyadic_polynomial_finite_shift
-- name    : OAI.SevenEighths.HeckePrimeDyadic.polynomial_finite_shift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:49:46.625013+00:00
-- url     : https://prove2.me/theorems/97a30ca2-c18e-483a-b061-8ac0a2795349
-- title:
--   Contour shift for the prime dyadic polynomial
-- statement:
--   Let $\chi$ be a `Character` with nontrivial residue character, $W$ smooth with support in $[a,b]$, $a>0$, and reals $D>0$, $\sigma$, `freq`, $l,r$ with $r+\sigma>1$, $T\ge0$, such that $L(\chi,s+\texttt{HeckeDyadic.shift}\,\sigma\,\mathrm{freq})\ne0$ on the rectangle $[l,r]\times[-T,T]$. Then, with $f=$`integrand χ W D σ freq`,
--   $$\texttt{polynomial}\,\chi\,W\,D\,\sigma\,\mathrm{freq}=\frac1{2\pi}\Big(\int_{-T}^Tf(l+it)\,dt+i\Big(\int_l^rf(x-iT)\,dx-\int_l^rf(x+iT)\,dx\Big)+\int_{[-T,T]^c}f(r+it)\,dt\Big).$$
--
--   Lean: `OAI.SevenEighths.HeckePrimeDyadic.polynomial_finite_shift` in `lean/OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicContour.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem polynomial_finite_shift (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1< r+σ) (hT : 0≤T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+HeckeDyadic.shift σ freq)≠0) :
    polynomial χ W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ W D σ freq ((r : ℂ)+t*I)) := by
  sorry

end SevenEighths.HeckePrimeDyadic

end

end OAI
end
