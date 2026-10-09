-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeDyadicReflection_original_reflected_subpower
-- name    : OAI.SevenEighths.HeckeDyadicReflection.original_reflected_subpower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:38:16.150987+00:00
-- url     : https://prove2.me/theorems/d16b19f2-955d-41ee-8dc0-e67a601be318
-- title:
--   Reflected bound for Hecke L-functions in the left half of the strip
-- statement:
--   For every $\varepsilon>0$ there is $C>0$ such that for every `Character` $\chi$ with nontrivial residue character and every $s$ with $-1/10\le\operatorname{Re}s\le1/2$,
--   $$|L(\chi,s)|\le C\,N(\chi.\mathrm{modulus})^{1/2-\operatorname{Re}s}\,N(\texttt{radical}\,\chi.\mathrm{modulus})^{\max(-\operatorname{Re}s,0)+2\varepsilon}(3+|\operatorname{Im}s|)^2\,|L(\chi,1-\bar s)|,$$
--   with `HeckeDeletionBounds.radical`.
--
--   Lean: `OAI.SevenEighths.HeckeDyadicReflection.original_reflected_subpower` in `lean/OAI/NumberTheory/DirichletL/Hecke/DyadicReflectedFamily.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B015

section

namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set
namespace SevenEighths.HeckeDyadicReflection
open HeckeFamily

theorem original_reflected_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ χ : Character, χ.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤ s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤C*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*
      ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
      (3+|s.im|)^2*‖LFunction χ (1-conj s)‖ := by
  sorry

end SevenEighths.HeckeDyadicReflection

end

end OAI
end
