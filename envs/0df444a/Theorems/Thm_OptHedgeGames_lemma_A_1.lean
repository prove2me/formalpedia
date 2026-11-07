-- Prove2me | Theorems.Thm_OptHedgeGames_lemma_A_1
-- name    : OptHedgeGames.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:39:27.019618+00:00
-- url     : https://prove2.me/theorems/53c41b86-1c74-4a3d-886d-ce37c1cc5ab6
-- title:
--   Lemma A.1 — variance facts: comparison, doubling, and range bounds
-- statement:
--   Let $p,p'$ be probability vectors on $n$ actions and $u,v\in\mathbb R^n$. Then:
--
--   1. if $p'(a)\le\Gamma p(a)$ for all $a$, then $\mathrm{Var}_{p'}(v)\le\Gamma\,\mathrm{Var}_p(v)$;
--   2. $\mathrm{Var}_p(u+v)\le2\mathrm{Var}_p(u)+2\mathrm{Var}_p(v)$;
--   3. $\mathrm{Var}_p(v)\le b^2/4$ whenever all entries of $v$ lie in an interval of length $b$;
--   4. $\mathrm{Var}_p(v)\le\|v\|_\infty^2$.
--
--   These facts let the analysis move a variance from one strategy to a nearby one.
--
--   Differences from the source:
--   - encoding: entries of v in an interval of length b → v a ∈ Set.Icc lo (lo + b) for all a; reason: the interval is written by its left end; same instances
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Lemma A.1, p.43

import Mathlib
import Definitions.Def_OptHedgeGames_Notation

namespace OptHedgeGames

/-- **Lemma A.1** (variance facts; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Lemma A.1, p.43). Let `p, p′` be probability vectors and
`u, v` real vectors. If `p′(a) ≤ Γp(a)` for all `a`, then `Var_{p′}(v) ≤ Γ Var_p(v)`. Moreover
`Var_p(u + v) ≤ 2 Var_p(u) + 2 Var_p(v)`, and `Var_p(v) ≤ b²/4` whenever all entries of `v` lie in an
interval of length `b`; in particular `Var_p(v) ≤ ∥v∥²_∞`.

**Formalization Note** Probability vectors are points of `stdSimplex ℝ (Fin n)`, which is empty at
`n = 0`. `∥v∥_∞` is the supremum norm of `Fin n → ℝ`. -/
theorem lemma_A_1 {n : ℕ} (p p' : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n))
    (hp' : p' ∈ stdSimplex ℝ (Fin n)) (u v : Fin n → ℝ) :
    (∀ Γ : ℝ, (∀ a, p' a ≤ Γ * p a) → var p' v ≤ Γ * var p v) ∧
      var p (u + v) ≤ 2 * var p u + 2 * var p v ∧
      (∀ lo b : ℝ, (∀ a, v a ∈ Set.Icc lo (lo + b)) → var p v ≤ b ^ 2 / 4) ∧
      var p v ≤ ‖v‖ ^ 2 := by sorry

end OptHedgeGames
