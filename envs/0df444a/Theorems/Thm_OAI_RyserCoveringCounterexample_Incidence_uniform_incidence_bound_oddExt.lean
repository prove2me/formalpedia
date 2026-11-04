-- Prove2me | Theorems.Thm_OAI_RyserCoveringCounterexample_Incidence_uniform_incidence_bound_oddExt
-- name    : OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound_oddExt
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-03T23:19:49.026012+00:00
-- url     : https://prove2.me/theorems/0d40d1a6-5170-47dc-98d3-d91a9040b0da
-- title:
--   Uniform incidence saving over fields with small proper subfields
-- statement:
--   Let $F$ be a finite field with $q=|F|$ elements, such that $q\ge Q$, where $Q$ is the absolute threshold `incidenceThreshold`, and every proper subfield $M$ of $F$ satisfies $|M|^3\le q$. Let $P$ be a finite set of points and $L$ a finite set of lines of the projective plane $\mathbb P^2(F)$, with $|P|,|L|\le q^{1+\kappa}$, where $\kappa=10^{-10}$ is the constant `savingExponent`. Then the number of incidences satisfies
--
--   $$
--   I(P,L)=\bigl|\{(p,\ell)\in P\times L : p\in\ell\}\bigr|\le q^{3/2-\kappa}.
--   $$
--
--   This is Theorem 2.1 of the paper, proved by the incidence and sum-product strategy of Bourgain, Katz and Tao. The bound is uniform over the field and its characteristic. It provides the power saving used to control intersections of a proposed line cover when no projective point lies on many of its lines.
-- source:
--   OpenAI, A counterexample to Ryser's covering conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Theorem 2.1. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/Incidence/Uniform.lean#L24 (declaration OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound; renamed here with suffix _oddExt because that name is taken by a copy stated over a different definitions module)

import Mathlib
import Definitions.Def_RyserOddSupport

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section

theorem uniform_incidence_bound_oddExt (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hq : incidenceThreshold ≤ Fintype.card F) (hsub : SmallProperSubfields F)
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (hP : (P.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 + savingExponent))
    (hL : (L.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 + savingExponent)) :
    (incidenceCount ProjectiveIncidence P L : ℝ) ≤
      (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - savingExponent) := by
  sorry

end
end RyserCoveringCounterexample.Incidence
end OAI
