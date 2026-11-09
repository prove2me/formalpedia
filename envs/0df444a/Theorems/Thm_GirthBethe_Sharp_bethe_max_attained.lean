-- Prove2me | Theorems.Thm_GirthBethe_Sharp_bethe_max_attained
-- name    : GirthBethe.Sharp.bethe_max_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:20:59.79255+00:00
-- url     : https://prove2.me/theorems/0632d5d9-90d7-46f4-8cd4-3427c4182760
-- title:
--   Equation (1.1) — the maximum defining $\mathrm{Bethe}(A)$ is attained
-- statement:
--   Let $n\ge1$, let $A\in\mathbb R^{n\times n}$ be nonnegative and suppose $\mathrm{PM}(G_A)\neq\emptyset$. Then the Bethe objective
--   $$p\longmapsto\prod_{e\in E(G_A)}\Big(\frac{A_e}{p_e}\Big)^{p_e}(1-p_e)^{1-p_e}$$
--   attains its supremum on $\mathrm{PM}(G_A)$, and that maximum is $\mathrm{Bethe}(A)$.
--
--   Definition (1.1) writes $\mathrm{Bethe}(A)$ as a maximum; this item certifies that the supremum used in the formal definition is that maximum.
--
--   **Formalization Note** Supporting item without a number of its own; it records the attainment presupposed by the word "max" in (1.1).
--
--   Differences from the source:
--   - encoding: A ∈ ℝ^{n×n}_{≥0} with rows and columns indexed by [n] → A : Matrix (Fin n) (Fin n) ℝ with ∀ i j, 0 ≤ A i j (0-based indices); reason: relabelling only
--   - encoding: Bethe(A) := max over PM(G_A) in (1.1) → bethe A := sSup of the Bethe objective over PM(G_A) (0 if PM(G_A) = ∅), real powers with x^0 = 1; reason: the maximum is attained (item bethe_max_attained), so the supremum is the maximum; real powers give the boundary values 1 at p_e = 0 and A_e at p_e = 1, which are the limits by continuity
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 2, §1.2, equation (1.1) (the maximum in the definition of Bethe(A)); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_BethePermanent

open Finset

namespace GirthBethe.Sharp

/-- Equation (1.1): when `PM(G_A) ≠ ∅` the maximum defining `Bethe(A)` is attained, and `Bethe(A)` is that maximum. -/
theorem bethe_max_attained (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hPM : (fracPM (supportEdges A)).Nonempty) :
    IsGreatest (betheObjective A '' fracPM (supportEdges A)) (bethe A) := by sorry

end GirthBethe.Sharp
