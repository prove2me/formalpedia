-- Prove2me | Theorems.Thm_Hintz2026_Dp_congr
-- name    : Hintz2026.Dp_congr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:07.92722+00:00
-- url     : https://prove2.me/theorems/3242d937-db38-4225-8ba5-5094d838839a
-- title:
--   D⁺ respects equality on U
-- statement:
--   If $f = g$ on $U$, then $D^+f(x) = D^+g(x)$ for all $x \in U$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/FieldInterface.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dp_congr (p : SubextremalKN) {f g : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ} (hU : x ∈ U p) (h : Set.EqOn f g (U p)) : Dp p f x = Dp p g x := by sorry
