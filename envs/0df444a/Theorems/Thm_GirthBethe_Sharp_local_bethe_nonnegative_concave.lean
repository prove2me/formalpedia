-- Prove2me | Theorems.Thm_GirthBethe_Sharp_local_bethe_nonnegative_concave
-- name    : GirthBethe.Sharp.local_bethe_nonnegative_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:15:24.646779+00:00
-- url     : https://prove2.me/theorems/36b33caa-af6a-4a73-970e-36986eb4f27b
-- title:
--   Lemma 2.3 — $S$ is nonnegative and concave on $\Delta_d$
-- statement:
--   For every $d\ge1$, the local Bethe entropy functional $S=H-H_c$ satisfies
--   $$S(q)\ge0\quad\text{for all }q\in\Delta_d,$$
--   and $S$ is concave on $\Delta_d$.
--
--   The two properties are used in the girth estimate (Lemma 4.2) and in the concavity of $\Gamma$ (Lemma 5.2).
--
--   Differences from the source:
--   - encoding: coordinates indexed by [d] = {1, …, d} → coordinates indexed by Fin d = {0, …, d-1}; reason: relabelling only
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 7, Lemma 2.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_LocalFunctionals

open Finset

namespace GirthBethe.Sharp

/-- Lemma 2.3: for every `d ≥ 1`, `S` is nonnegative and concave on `Δ_d`. -/
theorem local_bethe_nonnegative_concave (d : ℕ) (hd : 1 ≤ d) :
    (∀ q ∈ stdSimplex ℝ (Fin d), 0 ≤ localBethe q) ∧
      ConcaveOn ℝ (stdSimplex ℝ (Fin d)) localBethe := by sorry

end GirthBethe.Sharp
