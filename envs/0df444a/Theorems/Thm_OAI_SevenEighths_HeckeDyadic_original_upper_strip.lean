-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeDyadic_original_upper_strip
-- name    : OAI.SevenEighths.HeckeDyadic.original_upper_strip
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:38:07.327985+00:00
-- url     : https://prove2.me/theorems/53c15438-30fe-472d-a448-63dfec93c4d5
-- title:
--   Convexity-type bound for Hecke L-functions on Re s >= -1/10
-- statement:
--   For every $\varepsilon>0$ there is $C>0$ such that for every `Character` $\chi$ with nontrivial residue character and every $s$ with $\operatorname{Re}s\ge-1/10$,
--   $$|L(\chi,s)|\le C\,N(\chi.\mathrm{modulus})^{3/5}\,N(\texttt{radical}\,\chi.\mathrm{modulus})^{1/10+\varepsilon}\,(3+|\operatorname{Im}s|)^2.$$
--
--   Lean: `OAI.SevenEighths.HeckeDyadic.original_upper_strip` in `lean/OAI/NumberTheory/DirichletL/Hecke/DyadicReflectedControl.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth HeckeDeletionBounds

theorem original_upper_strip (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ χ : Character, χ.residue≠1 → ∀ s : ℂ,
      -(1/10 : ℝ)≤ s.re →
      ‖LFunction χ s‖≤C*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
        ((radical χ.modulus).absNorm : ℝ)^(1/10+ε)*(3+|s.im|)^2 := by
  sorry

end SevenEighths.HeckeDyadic

end

end OAI
end
