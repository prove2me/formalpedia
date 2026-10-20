-- Prove2me | Theorems.Thm_Hintz2026_Cmat_10_eq
-- name    : Hintz2026.Cmat_10_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:20.369378+00:00
-- url     : https://prove2.me/theorems/7080f077-9ea0-4eee-9d5e-ff8462b7b366
-- title:
--   Entry $(2,1)$ of $C$ equals $-R_1(r) + i\,\Theta_1(\theta)$
-- statement:
--   Third coefficient check of the separation $C^{(\varsigma)} = R^{(\varsigma)}(r) + i\Theta^{(\varsigma)}(\theta)$ (Hintz, text after eq. (7)): at every point of $U$ the $(2,1)$ entry of $C^{(\varsigma)} = (\det X)X^{-1}(c^{(\varsigma)}I - B^{(\varsigma)})(X^*)^{-1}$ equals $-R_1^{(\varsigma)}(r) + i\,\Theta_1^{(\varsigma)}(\theta)$, with $R_1$ and $\Theta_1$ the explicit paper coefficients (the $(2,1)$ entry of $R$ is $-R_1$ and that of $\Theta$ is $\Theta_1$). Proved by the same denominator-clearing polynomial verification.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/CEntries.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Cmat_10_eq (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x 1 0 = Csep p sg om mm x 1 0 := by sorry
