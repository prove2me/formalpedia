-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentPlainGlobalActual_global_polynomial_bound
-- name    : OAI.SevenEighths.CenteredMomentPlainGlobalActual.global_polynomial_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:45:56.358142+00:00
-- url     : https://prove2.me/theorems/9c088e08-9e21-4c61-9b8d-fac3e64fe876
-- title:
--   Polynomial bound for the smoothed Hecke sum
-- statement:
--   For reals $a>0$ and $b$ there are a finite $S\subseteq\mathbb N\times\mathbb N$ and $C>0$ such that for every Schwartz function $W$ supported in $[a,b]$, every `Character` $\chi$ with nontrivial residue character, and all reals $D\ge1$ and `freq`,
--   $$\|\texttt{polynomial}\ \chi\ \mathrm{false}\ W\ D\ 0\ \mathrm{freq}\|\le C\cdot\sup_S(\text{seminorms of }W)\cdot N(\chi.\mathrm{modulus})\cdot(3+|\mathrm{freq}|)^2.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentPlainGlobalActual.global_polynomial_bound` in `lean/OAI/NumberTheory/DirichletL/Moments/PlainGlobalActual.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
namespace SevenEighths.CenteredMomentPlainGlobalActual
open HeckeFamily HeckeDyadic

 theorem global_polynomial_bound (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀W:SchwartzMap ℝ ℂ,Function.support (W:ℝ→ℂ)⊆Icc a b→
    ∀χ:Character,χ.residue≠1→∀D freq:ℝ,1≤D→
      ‖polynomial χ false W D 0 freq‖≤
        C*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (χ.modulus.absNorm:ℝ)*(3+|freq|)^2:= by
  sorry

end SevenEighths.CenteredMomentPlainGlobalActual

end

end OAI
end
