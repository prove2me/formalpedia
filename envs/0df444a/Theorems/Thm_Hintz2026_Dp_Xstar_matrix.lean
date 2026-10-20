-- Prove2me | Theorems.Thm_Hintz2026_Dp_Xstar_matrix
-- name    : Hintz2026.Dp_Xstar_matrix
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:28.966099+00:00
-- url     : https://prove2.me/theorems/bfad730e-1cdc-4a0d-b68b-3b54b8afaa73
-- title:
--   $D^+$ of the conjugate transpose of $X$: $D^+(X^*) = X^*A$
-- statement:
--   On $U$, the conjugate transpose $X^*$ of the integrating factor satisfies
--
--   $$D^+\bigl(X^*\bigr) = X^*\,A, \qquad D^+ = \sqrt{\Delta}\,\partial_r + i\,\partial_\theta,$$
--
--   entrywise. It follows from $D^-X = AX$ by complex conjugation of each entry ($D^+\overline{f} = \overline{D^-f}$) together with $A^* = A$. This is the derivative rule for the transformed variable $z_- = X^*y_-$ of Hintz eq. (7).
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/AdjDeriv.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dp_Xstar_matrix (p : SubextremalKN) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : (of fun a b => Dp p (fun z => (X p z)ᴴ a b) x) = (X p x)ᴴ * A p x := by sorry
