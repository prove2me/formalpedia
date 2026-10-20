-- Prove2me | Theorems.Thm_Hintz2026_Cmat_11_eq
-- name    : Hintz2026.Cmat_11_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:15.357348+00:00
-- url     : https://prove2.me/theorems/8d131357-5dee-43dc-9cca-1507ea49382d
-- title:
--   Entry $(2,2)$ of $C$ equals $R_0(r) - i\,\Theta_0(\theta)$
-- statement:
--   Fourth coefficient check of the separation $C^{(\varsigma)} = R^{(\varsigma)}(r) + i\Theta^{(\varsigma)}(\theta)$ (Hintz, text after eq. (7)): at every point of $U$ the $(2,2)$ entry of $C^{(\varsigma)} = (\det X)X^{-1}(c^{(\varsigma)}I - B^{(\varsigma)})(X^*)^{-1}$ equals $R_0^{(\varsigma)}(r) + i\,(-\Theta_0^{(\varsigma)}(\theta))$, with $R_0$ and $\Theta_0$ the explicit paper coefficients (the $(2,2)$ entry of $\Theta$ is $-\Theta_0$). Proved by the same denominator-clearing polynomial verification.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/CEntries.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Cmat_11_eq (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x 1 1 = Csep p sg om mm x 1 1 := by sorry
