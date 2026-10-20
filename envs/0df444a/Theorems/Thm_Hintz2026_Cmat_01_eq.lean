-- Prove2me | Theorems.Thm_Hintz2026_Cmat_01_eq
-- name    : Hintz2026.Cmat_01_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:54:26.597434+00:00
-- url     : https://prove2.me/theorems/6ff98994-6321-44c5-9f34-4e288031af0f
-- title:
--   Entry $(1,2)$ of $C$ equals $R_1(r) + i\,\Theta_1(\theta)$
-- statement:
--   Second coefficient check of the separation $C^{(\varsigma)} = R^{(\varsigma)}(r) + i\Theta^{(\varsigma)}(\theta)$ (Hintz, text after eq. (7)). With the explicit formulas
--
--   $$R_1^{(\varsigma)}(r) = -\varsigma\,\frac{2\omega Q(Mr-Q^2)}{M^2-Q^2} + \frac{3iM}{2Q},\qquad \Theta_1^{(\varsigma)}(\theta) = -\varsigma\,\frac{2a\omega MQ\cos\theta}{M^2-Q^2} - \frac{3M}{2Q},$$
--
--   the theorem states that at every point of $U$ the $(1,2)$ entry of $C^{(\varsigma)} = (\det X)X^{-1}(c^{(\varsigma)}I - B^{(\varsigma)})(X^*)^{-1}$ equals $R_1^{(\varsigma)}(r) + i\,\Theta_1^{(\varsigma)}(\theta)$. The proof is the same denominator-clearing polynomial verification as for the $(1,1)$ entry.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/CEntries.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Cmat_01_eq (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x 0 1 = Csep p sg om mm x 0 1 := by sorry
