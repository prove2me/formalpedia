-- Prove2me | Theorems.Thm_OWMR_arb_local_comparison
-- name    : OWMR.arb_local_comparison
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:32.347287+00:00
-- url     : https://prove2.me/theorems/7b97dc09-89db-4077-ba40-090d53c7e022
-- title:
--   Lemma C.6 (local cost comparison): the two numerical inequalities behind $B_m$
-- statement:
--   Let $m\ge1$ and put $\bar\gamma_m=13/3+32/(57m)$, $g_m=\bar\gamma_m/2$, $\zeta_m=g_m/(g_m-1)$, $B_m=2(g_m-1)$ and $u_m=3\zeta_m(1+1/m)/\bigl(4(4+\zeta_m/m)\bigr)$, as in (33). For every real $u$, with
--   $$R(u)=\frac38\cdot\frac{1-u}{1-u/\bigl(\zeta_m(B_m-1+u)\bigr)},$$
--   1. if $0\le u\le u_m$, then $1+\frac{7(1+1/m)}{16}+\Bigl(\frac{14}{3\zeta_m}-1\Bigr)u+R(u)\le B_m$;
--   2. if $u_m\le u\le1$, then $1+\frac{7(1+1/m)}{8}+\Bigl(\frac{7}{3\zeta_m}-1-\frac{7}{12m}\Bigr)u+R(u)\le B_m$.
--
--   These are the two branches of the comparison in Lemma C.6 (half window when the setup share $u$ is at most $u_m$, the canonical optimum otherwise).
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix C, Step 6, Lemma C.6 with (C.24)-(C.28), pp. E.18-E.20; parameters (33), p. 27.

import Definitions.Def_owmr_consolidation_policy

open scoped ENNReal

namespace OWMR
theorem arb_local_comparison (m : ℝ) (hm : 1 ≤ m) (u : ℝ) :
    (0 ≤ u → u ≤ conU m →
      1 + 7 * (1 + 1 / m) / 16 + (14 / (3 * conZeta m) - 1) * u
        + 3 / 8 * ((1 - u) / (1 - u / (conZeta m * (conB m - 1 + u)))) ≤ conB m) ∧
    (conU m ≤ u → u ≤ 1 →
      1 + 7 * (1 + 1 / m) / 8 + (7 / (3 * conZeta m) - 1 - 7 * (1 / m) / 12) * u
        + 3 / 8 * ((1 - u) / (1 - u / (conZeta m * (conB m - 1 + u)))) ≤ conB m) := by sorry
end OWMR
