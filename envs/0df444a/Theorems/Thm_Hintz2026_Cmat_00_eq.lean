-- Prove2me | Theorems.Thm_Hintz2026_Cmat_00_eq
-- name    : Hintz2026.Cmat_00_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:20.600078+00:00
-- url     : https://prove2.me/theorems/97d572f2-c42b-414e-a07f-88555482a641
-- title:
--   Entry $(1,1)$ of $C$ equals $R_0(r) + i\,\Theta_0(\theta)$
-- statement:
--   This is the first of the four coefficient checks behind the separation claim $C^{(\varsigma)}(r,\theta) = R^{(\varsigma)}(r) + i\,\Theta^{(\varsigma)}(\theta)$ of Hintz (text after eq. (7)). With $C^{(\varsigma)} = (\det X)X^{-1}(c^{(\varsigma)}I - B^{(\varsigma)})(X^*)^{-1}$ defined from the data of eqs. (4)–(5), and with the independent explicit formulas
--
--   $$R_0^{(\varsigma)}(r) = \frac{3\Delta'}{4\sqrt{\Delta}} - i\varsigma\sqrt{\Delta}\Bigl(\frac{K}{\Delta} - \frac{2\omega Q^2}{M^2-Q^2}\Bigr),\qquad \Theta_0^{(\varsigma)}(\theta) = \tfrac32\cot\theta + \varsigma\Bigl(\frac{m}{\sin\theta} - \frac{a\omega(M^2+Q^2)\sin\theta}{M^2-Q^2}\Bigr),$$
--
--   ($K = -(r^2+a^2)\omega + am$, $\Delta' = 2(r-M)$), the theorem states that at every point of $U$ the $(1,1)$ entry of $C^{(\varsigma)}$ equals $R_0^{(\varsigma)}(r) + i\,\Theta_0^{(\varsigma)}(\theta)$. The proof multiplies by the constant $\det X = Q^2-M^2$, expands the triple product $\operatorname{adj}(X)(cI-B)\operatorname{adj}(X)^*$ entrywise, clears the denominators $\bar\rho,\bar\rho^*,\Delta,\sqrt\Delta,\sin\theta,Q,M^2-Q^2$ (all nonzero on $U$), and reduces powers of $\sqrt\Delta$, $\cos\theta$ and $i$ with $\sqrt\Delta^2=\Delta$, $\cos^2\theta = 1-\sin^2\theta$, $i^2=-1$; the two sides then agree as polynomial identities.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/CEntries.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Cmat_00_eq (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x 0 0 = Csep p sg om mm x 0 0 := by sorry
