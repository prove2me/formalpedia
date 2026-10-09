-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeDyadic_polynomial_bound_of_rectangle
-- name    : OAI.SevenEighths.HeckeDyadic.polynomial_bound_of_rectangle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:46:18.032219+00:00
-- url     : https://prove2.me/theorems/c08dfa80-3433-4f79-a882-9d0ef2c2f562
-- title:
--   Smoothed Hecke sum bounded by a rectangle contour estimate
-- statement:
--   Let $\chi$ be a `Character` with nontrivial residue character, `inverse` a Boolean, $W$ smooth with support in $[a,b]$, $a>0$, reals $D\ge1$, $\sigma$, `freq`, $l\le r$ with $r+\sigma>1$, $T\ge0$, $C_2,C_n,K\ge0$, $n\in\mathbb N$. Assume $(1+|t|)^2|\mathcal MW(l+it)|\le C_2$ for all $t$; $(1+|t|)^{n+2}|\mathcal MW(x+it)|\le C_n$ for $x\in[l,r]$ and all $t$; when `inverse` is true, $L(\chi,s+\texttt{shift}\,\sigma\,\mathrm{freq})\ne0$ on the rectangle $[l,r]\times[-T,T]$; and $\|\texttt{series}\,\chi\,\mathrm{inverse}\,(s+\texttt{shift}\,\sigma\,\mathrm{freq})\|\le K$ there. Then
--   $$\|\texttt{polynomial}\,\chi\,\mathrm{inverse}\,W\,D\,\sigma\,\mathrm{freq}\|\le\frac1{2\pi}\Big(C_2D^{l+\sigma-1/2}K\pi+2\frac{C_nD^{r+\sigma-1/2}K}{(1+T)^n}|r-l|+\frac{C_nD^{r+\sigma-1/2}\,\texttt{HeckeReciprocalBound.bound}(r+\sigma)}{(1+T)^n}\pi\Big).$$
--   Here $\mathcal MW$ is the Mellin transform `mellin W`.
--
--   Lean: `OAI.SevenEighths.HeckeDyadic.polynomial_bound_of_rectangle` in `lean/OAI/NumberTheory/DirichletL/Hecke/DyadicPointwise.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B016

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem polynomial_bound_of_rectangle (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤ r) (hr : 1< r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  sorry

end SevenEighths.HeckeDyadic

end

end OAI
end
