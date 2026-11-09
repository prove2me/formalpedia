-- Prove2me | Theorems.Thm_GirthBethe_Sharp_permutation_information_inequality
-- name    : GirthBethe.Sharp.permutation_information_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:15:19.168768+00:00
-- url     : https://prove2.me/theorems/079e70ae-bf7b-4558-ad15-21e195304eaf
-- title:
--   Lemma 5.3 — information inequality for random permutations
-- statement:
--   Let $X=(X_1,\dots,X_d)$ be a random permutation of $[d]$, with an arbitrary (not necessarily uniform) law. Then for every $j\in[d]$,
--   $$\sum_{i=1}^d I_\Gamma(X_j;X_i)\ \ge\ S\big(\mathcal L(X_j)\big).$$
--
--   Applied to the matching bijection and its inverse it gives the permutation estimate, Proposition 3.5.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [d] = {1, …, d} → coordinates indexed by Fin d = {0, …, d-1}; reason: relabelling only
--   - encoding: a random permutation X of [d] → a probability vector ν on Equiv.Perm (Fin d), with X_i(π) = π i; reason: the same object
--   - encoding: conditional laws L(X_j | X_i = a) in I_Γ → condLaw uses the unconditional law when P(X_i = a) = 0; reason: the expectation assigns weight zero to that observation; arbitrary permutation laws, including point masses, remain allowed
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 18, Lemma 5.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_LocalFunctionals
import Definitions.Def_GirthBethe_Sharp_FiniteInfo

open Finset

namespace GirthBethe.Sharp

/-- Lemma 5.3: for a random permutation `X` of `[d]` with arbitrary law and every `j`, `∑_i I_Γ(X_j; X_i) ≥ S(L(X_j))`. -/
theorem permutation_information_inequality (d : ℕ) (ν : Equiv.Perm (Fin d) → ℝ) (hν : ν ∈ stdSimplex ℝ (Equiv.Perm (Fin d)))
    (j : Fin d) :
    localBethe (law ν (fun π => π j)) ≤
      ∑ i, infoGain gammaFun ν (fun π => π j) (fun π => π i) := by sorry

end GirthBethe.Sharp
