-- Prove2me | Theorems.Thm_GirthBethe_Sharp_gamma_deletion_identity
-- name    : GirthBethe.Sharp.gamma_deletion_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:14:31.462572+00:00
-- url     : https://prove2.me/theorems/92287bcc-04ba-49a7-9617-6b8c2b0e26d8
-- title:
--   Lemma 5.1 — deletion identity for $\Gamma$
-- statement:
--   For every $q\in\Delta_d$,
--   $$d\,\Gamma(q)=S(q)+\sum_{a=1}^d(1-q_a)\,\Gamma(q^{\setminus a}),$$
--   where $q^{\setminus a}=(q_i/(1-q_a))_{i\ne a}\in\Delta_{d-1}$ and a summand with $q_a=1$ is interpreted as $0$.
--
--   The recursion gives the concavity of $\Gamma$ and the permutation information inequality.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [d] = {1, …, d} → coordinates indexed by Fin d = {0, …, d-1}; reason: relabelling only
--   - encoding: q^{\a} ∈ Δ_{d-1} → deletion q a indexed by the coordinates {i // i ≠ a}; reason: relabelling of Δ_{d-1}; Γ is invariant under relabelling
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 17, Lemma 5.1, equation (5.1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_LocalFunctionals

open Finset

namespace GirthBethe.Sharp

/-- Lemma 5.1: `d Γ(q) = S(q) + ∑_a (1 - q_a) Γ(q^{\a})` for every `q ∈ Δ_d` (a term with `q_a = 1` is zero). -/
theorem gamma_deletion_identity (d : ℕ) (q : Fin d → ℝ) (hq : q ∈ stdSimplex ℝ (Fin d)) :
    (d : ℝ) * gammaFun q = localBethe q + ∑ a, weightedDeletion q a := by sorry

end GirthBethe.Sharp
