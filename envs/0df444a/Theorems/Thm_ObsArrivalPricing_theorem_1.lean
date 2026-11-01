-- Prove2me | Theorems.Thm_ObsArrivalPricing_theorem_1
-- name    : ObsArrivalPricing.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:42:54.814059+00:00
-- url     : https://prove2.me/theorems/b2375299-d603-476e-adfd-eb4581d3fb0e
-- title:
--   Theorem 1 — the value of observability is at most $-\frac{2W_{-1}(-1/(2\sqrt e))+1}{(e^{W_{-1}(-1/(2\sqrt e))+1/2}-1)^2}\approx4.911$
-- statement:
--   Consider every instance of the model: a valuation law $F$ on $[0,\bar v]$ ($\bar v\ge0$), an arrival-time law $G$ on $[0,\infty)$ of total mass at most $1$ (the missing mass is "never arrives"), and discount rates $0\le\delta<\mu$. Let $R$ be the seller's optimal expected revenue when she observes the buyer's arrival time and $R^{uo}$ her optimal expected revenue when she does not. Let
--   $$C=-\frac{2W_{-1}\!\big(-\tfrac1{2\sqrt e}\big)+1}{\Big(e^{W_{-1}(-\frac1{2\sqrt e})+\frac12}-1\Big)^2}\approx 4.9108,$$
--   with $W_{-1}$ the negative branch of the Lambert function. Then
--
--   1. for every instance, $R\le C\,R^{uo}$;
--   2. the value of observability satisfies
--   $$VO=\sup_{G,F,\delta,\mu}\frac{R}{R^{uo}}\;\le\;C;$$
--   3. $C<4.911$.
--
--   For any valuation distribution and arrival time distribution, observing the buyer's arrival time therefore raises the seller's optimal revenue by a factor of at most $4.911$.
--
--   Differences from the source:
--   - generalization: valuation and arrival-time densities $f$, $g$ (p.8) → any laws $F$ on $[0,\bar v]$ and $G$ on $[0,\infty)$ of mass $\le1$ (atoms allowed); reason: the paper's instances are special cases; Theorem 1 says "any valuation distribution and arrival time distribution"
--   - generalization: "the value of observability is at most $C\approx4.911$" → three clauses: $R\le C\,R^{uo}$ per instance, $VO\le C$, and $C<4.911$; reason: the second clause is the printed statement; the first implies it and the third is the printed $\approx4.911$ as an upper bound
--   - encoding: $VO(G,F,\delta,\mu)=R/R^{uo}$ → a quotient in $[0,\infty]$ ($0/0=0$, $x/0=\infty$ for $x>0$), supremum over all instances; reason: never a real division, which would set $R/0=0$
--   - encoding: $R$ as the value of $[SPO_0]$ integrated against $g$, and $R^{uo}$ as the value of $[SPN]$ → $R=R_0\int e^{-\delta\tau}dG$ (p.11) and $R^{uo}$ the supremum over admissible deterministic prices of the lower Lebesgue integral of the revenue; reason: the paper's own formula for $R$; $[SPN]$'s integrand is written for continuous $p$ "just for simplicity" (p.12)
-- source:
--   Correa, Pizarro & Vulcano, The Value of Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), Theorem 1 and its proof, p.23; definitions of R, Ruo and VO, pp.11–13

import Mathlib
import Definitions.Def_ObsArrivalPricing_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ObsArrivalPricing

/-- Theorem 1 (SSRN 3541494, p.23): "For any valuation distribution and arrival time distribution,
the value of observability is at most −(2W₋₁(−1/(2√e))+1)/(e^{W₋₁(−1/(2√e))+1/2}−1)² ≈ 4.911."
For every instance `R ≤ C·Ruo`; hence `VO = sup R/Ruo ≤ C`; and `C < 4.911`. -/
theorem theorem_1 :
    (∀ I : ProblemInstance, R I ≤ ENNReal.ofReal voBound * Ruo I) ∧
      VO ≤ ENNReal.ofReal voBound ∧ voBound < 4.911 := by sorry

end ObsArrivalPricing
