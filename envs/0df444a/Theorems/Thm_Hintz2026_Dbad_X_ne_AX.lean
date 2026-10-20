-- Prove2me | Theorems.Thm_Hintz2026_Dbad_X_ne_AX
-- name    : Hintz2026.Dbad_X_ne_AX
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:01.592065+00:00
-- url     : https://prove2.me/theorems/66257739-db5e-4001-87ff-f2653f525245
-- title:
--   Wrong operator Dbad fails integrating factor equation
-- statement:
--   For any $x \in U$ with $a \neq 0$: the matrix $(\text{Dbad}\,X_{ij}(x))_{ij} \neq A(x)X(x)$, where $\text{Dbad} = \sqrt{\Delta}\partial_r$. This proves that deleting the angular-derivative term changes the integrating-factor equation when $a\ne0$; the theorem does not separately test deletion of the radial term.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/Residual.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dbad_X_ne_AX (p : SubextremalKN) {x : Fin 2 → ℝ} (hx : x ∈ U p) (ha : p.a ≠ 0) : (of fun i j => Dbad p (fun z => X p z i j) x) ≠ A p x * X p x := by sorry
