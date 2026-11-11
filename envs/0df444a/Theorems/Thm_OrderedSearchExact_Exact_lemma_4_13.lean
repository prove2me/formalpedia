-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_lemma_4_13
-- name    : OrderedSearchExact.Exact.lemma_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:59.764945+00:00
-- url     : https://prove2.me/theorems/fff78b85-6eb9-4800-aca4-454fa29dacb9
-- title:
--   Lemma 4.13 — full bound for the greedy recurrence
-- statement:
--   Fix $n$, $W,d>0$, $0<\rho<1$, and $M\ge1$ (the assumption $Dn\ge M\ge1$ forces $n\ge1$). Let $h=h_W$ satisfy (28), suppose $\tanh(M/2)>\rho^2$, and let $D$ satisfy the sufficient large-rate numerical criterion from Lemma 4.12. Assume $Dn\ge M$. Then some greedy prefix reaches coefficient mass less than one and its concrete exactification terminates within
--
--   $$1+\left\lceil\frac{2W+\ln M}{\ln3}\right\rceil+\left\lceil\frac{\ln(Dn/M)}d\right\rceil+3$$
--
--   queries. The statement includes prefix feasibility and exact termination, and covers early infinite greedy jumps. Both ceilings and the initial, synchronization, and exactifier queries are retained.
--
--   Differences from the source:
--   - encoding: normalized real symmetric Laurent polynomials of degree less than n → real coefficient vectors indexed by Fin (n-1), with frequency i+1 and evaluation on every real angle; reason: this bijects the source coefficients, preserves the constant coefficient 1, and includes all points of the unit circle
--   - reading: D is the sufficiently large fixed constant furnished by Lemma 4.12 → D>0 and 4/((exp D-1)(1-exp(-4D)))<1; reason: this makes the unquantified phrase sufficiently large operational using the precise uniform bound in that lemma proof; D=2 is included
--   - encoding: reaches (41), and hence 1, within the displayed query bound → there exists a greedy prefix length t with t+2 at most the bound, mass<1, and feasible explicit exactification; reason: t names the hybrid reached before the two final parity-respecting queries
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Lemma 4.13, p.23 (PDF p.23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Greedy

namespace OrderedSearchExact.Exact

theorem lemma_4_13 (n : ℕ) (W d ρ M D : ℝ)
    (hW : 0 < W) (hd : 0 < d) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hc : Certificate (quarticDensity W) d ρ)
    (ht : ρ ^ 2 < Real.tanh (M / 2)) (hD : DecayConstant D)
    (hM : 1 ≤ M) (hnM : M ≤ D * n) :
    ∃ t : ℕ, t + 2 ≤ queryBudget n W d M D ∧
      FeasiblePrefix n t (greedyPath n (quarticDensity W)) ∧
      mass (greedyPath n (quarticDensity W) t) < 1 ∧
      FeasiblePath n (t + 2) (exactify (greedyPath n (quarticDensity W)) t) := by sorry

end OrderedSearchExact.Exact
