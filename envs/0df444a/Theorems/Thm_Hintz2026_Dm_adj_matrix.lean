-- Prove2me | Theorems.Thm_Hintz2026_Dm_adj_matrix
-- name    : Hintz2026.Dm_adj_matrix
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:14.782753+00:00
-- url     : https://prove2.me/theorems/45102d22-ec1c-444f-9bc1-55461a3d14e2
-- title:
--   $D^-$ of the adjugate of $X$: $D^-(\operatorname{adj}X) = -(\operatorname{adj}X)\,A$
-- statement:
--   Let $X(r,\theta)$ be the matrix integrating factor of Hintz eq. (5) and $A$ the Hermitian coefficient matrix of eq. (4), on the domain $U = \{r > r_+,\ 0<\theta<\pi\}$ of a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$). Since $\det X = Q^2 - M^2$ is a nonzero constant on $U$, the adjugate satisfies $\operatorname{adj}X = (Q^2-M^2)\,X^{-1}$ there, and the integrating-factor equation $D^-X = AX$ transports to
--
--   $$D^-\bigl(\operatorname{adj}X\bigr) = -\,(\operatorname{adj}X)\,A \qquad\text{on } U,$$
--
--   where $D^- = \sqrt{\Delta}\,\partial_r - i\,\partial_\theta$ acts entrywise. This is the derivative rule needed for the transformed variable $z_+ = (\operatorname{adj}X)\,y_+$ of eq. (7).
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/AdjDeriv.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dm_adj_matrix (p : SubextremalKN) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : (of fun a b => Dm p (fun z => adjugate (X p z) a b) x) = -(adjugate (X p x) * A p x) := by sorry
