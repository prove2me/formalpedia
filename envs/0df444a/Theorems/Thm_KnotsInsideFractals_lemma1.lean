-- Prove2me | Theorems.Thm_KnotsInsideFractals_lemma1
-- name    : KnotsInsideFractals.lemma1
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T15:07:56.841838+00:00
-- url     : https://prove2.me/theorems/b8229774-d6df-52d5-82be-5ef9a5e0c550
-- title:
--   Lemma 1 — Cantor dust lifts through the sponge
-- statement:
--   **Lemma 1.** If $(x,y)$ is a point of the Cantor dust $C\times C$ and $z\in[0,1]$, then $(x,y,z)$ belongs to the Menger sponge $M$:
--   $$(x,y)\in C\times C,\ z\in[0,1]\ \Longrightarrow\ (x,y,z)\in M.$$
--   Geometrically, the vertical segment above a Cantor-dust point of the front face passes straight through the sponge to the back face, avoiding every hole. This is the key fact that lets the proof of Theorem 1 join the front-face and back-face portions of the knot.
-- source:
--   Broden–Espinosa–Nazareth–Voth, Knots Inside Fractals, https://arxiv.org/abs/2409.03639, §3 Lemma 1

import Mathlib
import Definitions.Def_KnotsInsideFractals_fractals
import Definitions.Def_KnotsInsideFractals_knots
open Set KnotsInsideFractals

namespace KnotsInsideFractals
theorem lemma1 (x y : ℝ) (h : (x, y) ∈ cantorDust) (z : ℝ) (hz : z ∈ Set.Icc 0 1) : (![x, y, z] : R3) ∈ mengerSet := by sorry
end KnotsInsideFractals
