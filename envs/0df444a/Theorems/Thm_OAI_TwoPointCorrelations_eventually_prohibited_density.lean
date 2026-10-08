-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_eventually_prohibited_density
-- name    : OAI.TwoPointCorrelations.eventually_prohibited_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:29.652423+00:00
-- url     : https://prove2.me/theorems/29cbd2f1-be9f-433e-8ef3-73630967ee04
-- title:
--   The deleted event of a prohibited prime family has probability at most exp(−½L^{199/200})
-- statement:
--   Let $C\ge0$. For all sufficiently large $L$: for all naturals $h,s,J,M,B,H$ and every prohibited prime family $F$ (`ProhibitedPrimeFamily h J M`) whose primes are at most $B$, if $1\le s\le L^{1/10}$, $s(J+M)\le Cs\log L$, $1\le\sum_{p\in F.P}1/p\le L^2$, $\sum_{p\in F.Q}1/p\le L^2$, $H\ge\exp(L^{199/200})$, $1\le B\le e^L$ and every prime of $F.P$ is at least $H$, then
--
--   $$\Pr_{F.\texttt{residueLaw}\,B}\big(F.\texttt{deletedEvent}\ s\ B\big)\le\exp\!\big(-\tfrac12L^{199/200}\big),$$
--
--   where the residue law and the deleted event are the bundle's definitions attached to the family.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.eventually_prohibited_density`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical
open Filter

theorem eventually_prohibited_density (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (h s J M B H : ℕ) (F : ProhibitedPrimeFamily h J M)
      (hB : ∀ p ∈ F.P ∪ F.Q, p ≤ B),
      1 ≤ s → (s : ℝ) ≤ L ^ (1 / 10 : ℝ) →
      ((s * (J + M) : ℕ) : ℝ) ≤ C * s * Real.log L →
      1 ≤ primeHarmonicMass F.P →
      primeHarmonicMass F.P ≤ L ^ (2 : ℕ) → primeHarmonicMass F.Q ≤ L ^ (2 : ℕ) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H → 1 ≤ B → (B : ℝ) ≤ Real.exp L →
      (∀ p ∈ F.P, H ≤ p) →
      (F.residueLaw B hB).probability (F.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
