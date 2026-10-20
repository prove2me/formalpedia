-- Prove2me | Theorems.Thm_Hintz2026_adjugate_Csep_eq
-- name    : Hintz2026.adjugate_Csep_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:42.488499+00:00
-- url     : https://prove2.me/theorems/1645e1b1-91de-4af2-a622-baa796ad0b7e
-- title:
--   $\operatorname{adj}(R + i\Theta) = R^{\mathsf T} - i\Theta$
-- statement:
--   Let $R^{(\varsigma)}(r) = \begin{pmatrix} R_0 & R_1 \\ -R_1 & R_0\end{pmatrix}$ and $\Theta^{(\varsigma)}(\theta) = \begin{pmatrix} \Theta_0 & \Theta_1 \\ \Theta_1 & -\Theta_0\end{pmatrix}$ be the radial and angular coefficient matrices written after Hintz eq. (7), with the explicit coefficients $R_0,R_1,\Theta_0,\Theta_1$ of the paper. Then for every $(r,\theta)$
--
--   $$\operatorname{adj}\bigl(R^{(\varsigma)}(r) + i\,\Theta^{(\varsigma)}(\theta)\bigr) = R^{(\varsigma)}(r)^{\mathsf T} - i\,\Theta^{(\varsigma)}(\theta),$$
--
--   the identity $\operatorname{adj}C = R^{\mathsf T} - i\Theta$ stated in the paper, proved directly from the $2\times 2$ adjugate formula and the symmetry pattern of $R$ and $\Theta$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/System8.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.adjugate_Csep_eq (p : SubextremalKN) (sg om mm : ℝ) (x : Fin 2 -> ℝ) : adjugate (Csep p sg om mm x) = (Rmat p sg om mm (x 0)).transpose - I • Thmat p sg om mm (x 1) := by sorry
