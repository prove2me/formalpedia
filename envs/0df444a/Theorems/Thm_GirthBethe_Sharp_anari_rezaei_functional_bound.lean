-- Prove2me | Theorems.Thm_GirthBethe_Sharp_anari_rezaei_functional_bound
-- name    : GirthBethe.Sharp.anari_rezaei_functional_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:14:45.769819+00:00
-- url     : https://prove2.me/theorems/1810dbb1-6bf8-44f3-a80b-25d77bbf9ce2
-- title:
--   Proposition 2.10 — $F(q)\le(\log2)/2$, with equality at $(1/2,1/2)$
-- statement:
--   For every $d\ge1$ and every $q\in\Delta_d$,
--   $$F(q)\le\frac{\log2}{2},$$
--   and equality is attained at $q=(1/2,1/2)\in\Delta_2$.
--
--   This is the sharp bound of Anari and Rezaei [4, Lemma 10], applied at the $2n$ vertices of $G_A$ in the proof of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [d] = {1, …, d} → coordinates indexed by Fin d = {0, …, d-1}; reason: relabelling only
--   - encoding: π uniform on Sym(d) → π uniform on Equiv.Perm (Fin d), F in the second form of Definition 2.8; reason: the two forms of Definition 2.8 are equal
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 8, Proposition 2.10 ([4, Lemma 10]); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_LocalFunctionals

open Finset

namespace GirthBethe.Sharp

/-- Proposition 2.10 ([4, Lemma 10]): `F(q) ≤ (log 2)/2` on every `Δ_d`, `d ≥ 1`, with equality at `(1/2, 1/2) ∈ Δ_2`. -/
theorem anari_rezaei_functional_bound :
    (∀ d : ℕ, 1 ≤ d → ∀ q ∈ stdSimplex ℝ (Fin d), anariRezaei q ≤ Real.log 2 / 2) ∧
      anariRezaei (![1 / 2, 1 / 2] : Fin 2 → ℝ) = Real.log 2 / 2 := by sorry

end GirthBethe.Sharp
