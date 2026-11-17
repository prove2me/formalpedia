-- Prove2me | Theorems.Thm_N25_etaResidueSeries25_trunc_prefix
-- name    : N25.etaResidueSeries25_trunc_prefix
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:59.717519+00:00
-- url     : https://prove2.me/theorems/ae13802a-4d56-4329-9d73-e920dca5dbda
-- title:
--   A finite product determines every sufficiently low truncation
-- statement:
--   Let $0<g<25$ and let $N,t\in\mathbb N$ satisfy $N\le25t$. The truncation of the residue power series $R_g$ through degree $N$ equals the same truncation of the first $t$ two-factor blocks:
--
--   $$\operatorname{trunc}_N(R_g)=\operatorname{trunc}_N\prod_{0\le m<t}(1-X^{25m+g})(1-X^{25(m+1)-g}).$$
--
--   This is the finite-prefix principle used by the coefficient certificates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open scoped BigOperators
open N25

theorem N25.etaResidueSeries25_trunc_prefix (g N t : ℕ)
    (hg : 0 < g) (hg25 : g < 25) (hNt : N ≤ 25 * t) :
    PowerSeries.trunc N (etaResidueSeries25 g) =
      PowerSeries.trunc N
        (∏ m ∈ Finset.range t,
          ((1 - PowerSeries.X ^ (25 * m + g)) *
            (1 - PowerSeries.X ^ (25 * (m + 1) - g)) : PowerSeries ℤ)) := by sorry
