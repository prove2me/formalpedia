-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_not_hadwiger_conjecture
-- name    : OAI.HadwigerCounterexample.not_hadwiger_conjecture
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T21:57:24.086327+00:00
-- url     : https://prove2.me/theorems/c48188c4-0191-4bd6-8581-8cd9573a5dcd
-- title:
--   Hadwiger's conjecture is false
-- statement:
--   The headline consequence announced in the abstract of the source preprint: Hadwiger's conjecture is false. Writing $h(G)$ for the Hadwiger number and $\chi(G)$ for the chromatic number, the conjecture asserts $\chi(G)\le h(G)$ for every finite simple graph; this theorem negates that universal statement:
--   $$\neg\,\forall m\;\forall G\text{ on }m\text{ vertices},\quad \chi(G)\le h(G).$$
--
--   It follows from the counterexamples of Corollary 1.2, where $h(G)<m/2\le\chi(G)$. The chromatic number is compared as an extended natural number (`ℕ∞`) against the natural Hadwiger number coerced to `ℕ∞`.
--
--   **Formalization Note.** Transcribed verbatim from the authors' Lean theorem `OAI.HadwigerCounterexample.not_hadwiger_conjecture` (`Main.lean`).
-- source:
--   https://github.com/openai/math/blob/main/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf , abstract and p. 3, Corollary 1.2; authors' Lean: https://github.com/openai/math/blob/main/lean/OAI/Combinatorics/HadwigerCounterexample/Main.lean

import Mathlib
import Definitions.Def_ListHadwiger

open OAI.LinearListHadwiger

namespace OAI.HadwigerCounterexample

theorem not_hadwiger_conjecture :
    ¬ (∀ (m : ℕ) (G : SimpleGraph (Fin m)),
      G.chromaticNumber ≤ ↑(hadwigerNumber G)) := by sorry

end OAI.HadwigerCounterexample
