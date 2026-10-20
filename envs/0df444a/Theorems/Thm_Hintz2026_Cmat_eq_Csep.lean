-- Prove2me | Theorems.Thm_Hintz2026_Cmat_eq_Csep
-- name    : Hintz2026.Cmat_eq_Csep
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:21.461986+00:00
-- url     : https://prove2.me/theorems/8229024e-ee04-431d-ae60-f368ee61a762
-- title:
--   Separation of the coupling matrix: $C^{(\varsigma)}(r,\theta) = R^{(\varsigma)}(r) + i\,\Theta^{(\varsigma)}(\theta)$
-- statement:
--   Let $C^{(\varsigma)} = (\det X)\,X^{-1}\bigl(c^{(\varsigma)}I - B^{(\varsigma)}\bigr)(X^*)^{-1}$ be the coupling matrix of Hintz eq. (7), built from the integrating factor $X$ of eq. (5) and the coefficients $c^{(\varsigma)}, B^{(\varsigma)}$ of eq. (4), for a subextremal Kerr–Newman background, real frequency $\omega$, real azimuthal number $m$ and real spin parameter $\varsigma$ (the paper's two spin systems are $\varsigma = \pm 1$). Let $R^{(\varsigma)}(r) = \begin{pmatrix} R_0 & R_1 \\ -R_1 & R_0\end{pmatrix}$ and $\Theta^{(\varsigma)}(\theta) = \begin{pmatrix} \Theta_0 & \Theta_1 \\ \Theta_1 & -\Theta_0\end{pmatrix}$ be the matrices with the explicit coefficients
--
--   $$R_0 = \frac{3\Delta'}{4\sqrt{\Delta}} - i\varsigma\sqrt{\Delta}\Bigl(\frac{K}{\Delta} - \frac{2\omega Q^2}{M^2-Q^2}\Bigr),\quad R_1 = -\varsigma\frac{2\omega Q(Mr-Q^2)}{M^2-Q^2} + \frac{3iM}{2Q},$$
--
--   $$\Theta_0 = \tfrac32\cot\theta + \varsigma\Bigl(\frac{m}{\sin\theta} - \frac{a\omega(M^2+Q^2)\sin\theta}{M^2-Q^2}\Bigr),\quad \Theta_1 = -\varsigma\frac{2a\omega MQ\cos\theta}{M^2-Q^2} - \frac{3M}{2Q}.$$
--
--   Then at every point $(r,\theta)\in U$
--
--   $$C^{(\varsigma)}(r,\theta) = R^{(\varsigma)}(r) + i\,\Theta^{(\varsigma)}(\theta).$$
--
--   This is the separation of variables that makes eq. (8) of the paper possible: the $r$-dependence and the $\theta$-dependence of the coupling split additively. The definitions of $R$ and $\Theta$ are independent of $C$; the theorem is the entrywise coefficient verification (four entry lemmas).
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/CEntries.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Cmat_eq_Csep (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x = Csep p sg om mm x := by sorry
