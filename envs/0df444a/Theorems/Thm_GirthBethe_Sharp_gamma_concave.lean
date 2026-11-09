-- Prove2me | Theorems.Thm_GirthBethe_Sharp_gamma_concave
-- name    : GirthBethe.Sharp.gamma_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:14:39.206326+00:00
-- url     : https://prove2.me/theorems/203add1f-2198-45ee-94f7-f2f5eacc6b5c
-- title:
--   Lemma 5.2 — $\Gamma$ is concave on $\Delta_d$
-- statement:
--   For every $d\ge1$, the functional $\Gamma=H-2H_c+2F:\Delta_d\to\mathbb R$ is concave.
--
--   Concavity is what allows the data-processing inequality, Lemma 2.7, to be applied to $\Gamma$.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [d] = {1, …, d} → coordinates indexed by Fin d = {0, …, d-1}; reason: relabelling only
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 18, Lemma 5.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_LocalFunctionals

open Finset

namespace GirthBethe.Sharp

/-- Lemma 5.2: for every `d ≥ 1`, `Γ` is concave on `Δ_d`. -/
theorem gamma_concave (d : ℕ) (hd : 1 ≤ d) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin d)) gammaFun := by sorry

end GirthBethe.Sharp
