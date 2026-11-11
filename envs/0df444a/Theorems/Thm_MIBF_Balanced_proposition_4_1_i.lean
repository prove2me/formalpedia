-- Prove2me | Theorems.Thm_MIBF_Balanced_proposition_4_1_i
-- name    : MIBF.Balanced.proposition_4_1_i
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:59:09.730858+00:00
-- url     : https://prove2.me/theorems/4d7fd1b5-5da6-43e7-a63e-39705886b1ad
-- title:
--   Proposition 4.1(i) — reflection: $\kappa(u,w)\le\kappa(1-u,w)$ for $u,w\in(0,\tfrac12]$
-- statement:
--   Let $\kappa(u,w)=j(u,w)-F\bigl(|u-w|,\frac{H(u)+H(w)}{2}\bigr)$ be the residual of the Jeffreys cost above its perspective part (bits; $j$ the interior Jeffreys cost, $F$ the perspective of `GeneralCK_bellman`, $H$ the binary entropy). Then for all $u,w\in(0,\tfrac12]$,
--   $$\kappa(u,w)\ \le\ \kappa(1-u,w).$$
--   Reflecting one endpoint across $\tfrac12$ keeps the entropy coordinates and does not decrease the residual; this is what lets the perspective lower bound treat cross-half atoms through their lower-half entropy representatives.
--
--   **Formalization Note** Stated in bits on the published `GeneralCK` functions.
--
--   Differences from the source:
--   - encoding: nats ($h$, natural-log $j$ and $F$) → bits ($H$, `GeneralCK.interiorCost`, `GeneralCK.F`); reason: $\kappa$ in bits is $\kappa$ in nats divided by $\ln 2$, so the inequality is the same at every point.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 10, Proposition 4.1(i), eq. (19); proof [Full] Supplementary Section S.20.2

import Mathlib
import Definitions.Def_MIBF_Balanced_PureGap

namespace MIBF.Balanced
theorem proposition_4_1_i (u w : ℝ) (hu : 0 < u ∧ u ≤ 1 / 2) (hw : 0 < w ∧ w ≤ 1 / 2) :
    kappa u w ≤ kappa (1 - u) w := by sorry
end MIBF.Balanced
