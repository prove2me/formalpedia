-- Prove2me | Theorems.Thm_MultivarScores_L2Rule_lpm_injective
-- name    : MultivarScores.L2Rule.lpm_injective
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:29.207223+00:00
-- url     : https://prove2.me/theorems/54d07627-fa9a-48ec-a89a-ad1ab52dff20
-- title:
--   App., p. 34 — lower partial moments of order k uniquely characterize distributions
-- statement:
--   Let $k\in\mathbb N$ and let $P_X,P_Y$ be probability distributions on $\mathbb R^d$ whose lower partial moments of order $k$,
--
--   $$\mathrm{LPM}_{X,k}(z)=\int_{\mathbb R^d}\prod_{j=1}^d\frac1{k!}(z_j-s_j)^k\,\mathbb 1\{z_j\ge s_j\}\,dP_X(s)$$
--
--   (and likewise $\mathrm{LPM}_{Y,k}$), are finite at every $z\in\mathbb R^d$. If $\mathrm{LPM}_{X,k}(z)=\mathrm{LPM}_{Y,k}(z)$ for every $z$, then $P_X=P_Y$.
--
--   This is the fact behind the paper's claim (p. 11) that the LPM scores LPMS and LPMS′ are strictly proper when $h$ is nonzero a.e.: by Theorem 1 with $w$ the LPM kernel, it remains to know that the LPM determines the distribution.
--
--   **Formalization Note** The finiteness hypotheses are necessary: $\mathrm{LPM}_{X,k}$ is infinite for heavy lower tails, and a Bochner integral would then be $0$, faking equality. At $k=0$ they hold automatically and $\mathrm{LPM}_{X,0}=F_X$. The appendix writes "if $\mathrm{LPMS}'(P_X,y;k,h)=\mathrm{LPMS}'(P_Y,y;k,h)$"; the argument it gives (and its opening sentence) concerns equality of the LPMs themselves, which is what is stated here.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 34, Appendix, Discussion of LPMs; p. 11, (7)

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

namespace MultivarScores.L2Rule

open MeasureTheory

/-- App., p. 34: lower partial moments of order `k` uniquely characterize distributions: if
`LPM_{X,k}(z) = LPM_{Y,k}(z)` for every `z` (both finite), then `P_X = P_Y`. -/
theorem lpm_injective {d : ℕ} (k : ℕ) (PX PY : Measure (E d))
    [IsProbabilityMeasure PX] [IsProbabilityMeasure PY]
    (hX : ∀ z : E d, Integrable
      (fun s : E d => ∏ j, ((z j - s j) ^ k / (k.factorial : ℝ) * if s j ≤ z j then 1 else 0)) PX)
    (hY : ∀ z : E d, Integrable
      (fun s : E d => ∏ j, ((z j - s j) ^ k / (k.factorial : ℝ) * if s j ≤ z j then 1 else 0)) PY)
    (heq : ∀ z, lpm k PX z = lpm k PY z) :
    PX = PY := by sorry

end MultivarScores.L2Rule
