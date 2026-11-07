-- Prove2me | Theorems.Thm_OnlineBinCover_observation_3_2
-- name    : OnlineBinCover.observation_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:35.646228+00:00
-- url     : https://prove2.me/theorems/2b01e4f7-dd50-4b73-974c-f66a4fa5a550
-- title:
--   Observation 3.2 — slot counts and $\mathrm{ALG}_{BP}(I)\le\mathrm{vol}(I_p)/p$
-- statement:
--   Let $I$ have sizes in $(0,1]$, let $J$ be a set of items (the sample $I_p$) with its classes $L_p,M_p,S_p$ and groups $G^p_j$, let $p>0$, and let $x$ be any feasible solution of the configuration LP (3) on $J$. The blueprint with $z_C=\lfloor\lfloor x_C\rfloor/p\rfloor$ bins of configuration $C$ satisfies
--
--   1. $\sum_C z_C\,n(j,C)\le|G^p_j|/p$ for every group $j$;
--   2. $\sum_C z_C\sum_j n(j,C)\le|L_p|/p$;
--   3. $\sum_C z_C\,d(C)\le\mathrm{vol}(S_p)/p$;
--   4. $\mathrm{ALG}_{BP}(I)=\sum_Cz_C\le\mathrm{vol}(I_p)/p$.
--
--   These counts compare the blueprint with the items that will fill it.
--
--   Differences from the source:
--   - generalization: the rounded basic solution $x^p_C$ of Lemma 2.2 on the sample → every feasible solution of (3), every item set $J$ and every $p>0$; reason: the bounds use feasibility only; specializes to the sample and its LP solution
--   - encoding: ties resolved consistently across $I$ and its subsets → ties broken by the item label; reason: a consistent rule, as p.6 requires
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Observation 3.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_OnlineBinCover_Blueprint

namespace OnlineBinCover

/-- Observation 3.2, p.8. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

For a sample `J` (ranks, classes and groups inside `J`), a fraction `p > 0` and any feasible
solution `x` of LP (3) on `J`, the blueprint with `z_C = ⌊⌊x_C⌋/p⌋` bins of configuration `C` uses
at most `|G^p_j|/p` slots of group `j`, at most `|Lp|/p` large slots in total, total S-slot demand
at most `vol(Sp)/p`, and `ALGBP ≤ vol(Ip)/p`. -/
theorem observation_3_2 {n : ℕ} (s : Fin n → ℝ) (hs : ValidSizes s) (J : Finset (Fin n))
    (ε p : ℝ) (hp : 0 < p) (x : (Fin (Kof ε) → ℕ) →₀ ℝ)
    (hx : LPFeasible (lpCnt s J ε) (rsize s J ε) (lpVolS s J ε) x) :
    (∀ j : Fin (Kof ε), ∑ C ∈ x.support, (zC x p C : ℝ) * (C j : ℝ) ≤
        ((Gp s J ε j).card : ℝ) / p) ∧
      ∑ C ∈ x.support, (zC x p C : ℝ) * ∑ j, (C j : ℝ) ≤ ((largeOf s J ε).card : ℝ) / p ∧
      ∑ C ∈ x.support, (zC x p C : ℝ) * demand (rsize s J ε) C ≤
        volOn s (smallOf s J ε) / p ∧
      (ALGBP x p : ℝ) ≤ volOn s J / p := by sorry

end OnlineBinCover
