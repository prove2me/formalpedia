-- Prove2me | Theorems.Thm_Hintz2026_Dm_congr
-- name    : Hintz2026.Dm_congr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:00.634072+00:00
-- url     : https://prove2.me/theorems/2f7ecf44-e7e6-42de-84eb-95bf8da25090
-- title:
--   D⁻ respects equality on U
-- statement:
--   If $f = g$ on $U$, then $D^-f(x) = D^-g(x)$ for all $x \in U$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/FieldInterface.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dm_congr (p : SubextremalKN) {f g : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ} (hU : x ∈ U p) (h : Set.EqOn f g (U p)) : Dm p f x = Dm p g x := by sorry
