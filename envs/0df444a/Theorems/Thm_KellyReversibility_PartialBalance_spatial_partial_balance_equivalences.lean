-- Prove2me | Theorems.Thm_KellyReversibility_PartialBalance_spatial_partial_balance_equivalences
-- name    : KellyReversibility.PartialBalance.spatial_partial_balance_equivalences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:00:41.355582+00:00
-- url     : https://prove2.me/theorems/3e7e2401-ecf4-435c-af6e-fd34cd0a1cea
-- title:
--   Corollary 9.6 — partial balance at a site ⇔ frozen equilibrium is the conditional law ⇔ rate change at the site ⇔ reversal and freezing commute
-- statement:
--   Let $\mathbf n(t)$ be a spatial process over a finite graph $G$, with finite attribute sets $\mathcal N_j$, state space $\mathcal S=\prod_j\mathcal N_j$, rates $q$, and equilibrium distribution $\pi$ (positive, summing to one, satisfying the equilibrium equations). Fix a site $j$ and a constant $c>0$, $c\ne1$. The following statements are equivalent.
--
--   1. $\pi$ satisfies the partial balance equations
--   $$\pi(\mathbf n)\sum_m q(\mathbf n,T_j^m\mathbf n)=\sum_m\pi(T_j^m\mathbf n)q(T_j^m\mathbf n,\mathbf n),\qquad\mathbf n\in\mathcal S.\tag{9.26}$$
--   2. For every $\mathbf n_{G-j}$, the equilibrium distribution of the truncated process $n_j$ obtained when the sites other than $j$ are frozen at $\mathbf n_{G-j}$ is the conditional distribution $P(n_j\mid\mathbf n_{G-j})=\pi(\mathbf n)/\sum_m\pi(T_j^m\mathbf n)$.
--   3. If every rate $q(\mathbf n,T_j^m\mathbf n)$ is changed to $c\,q(\mathbf n,T_j^m\mathbf n)$, the resulting process has the unaltered equilibrium distribution $\pi$.
--   4. For every $\mathbf n_{G-j}$, reversing time and freezing the sites other than $j$ at $\mathbf n_{G-j}$ commute: the time reversal of the frozen process (with respect to its equilibrium distribution) has the rates of the frozen time reversal $\pi(\mathbf m)q(\mathbf m,\mathbf n)/\pi(\mathbf n)$.
--
--   Applied for every site, statement 2 shows the equilibrium distribution is a Markov field (Corollary 9.7).
--
--   **Formalization Note** "The equilibrium distribution" is the unique positive normalized solution of the equilibrium equations; the frozen and altered processes are irreducible by condition (iii) of a spatial process, so it exists and is unique. The book's "$c\ne0$ or $1$" is read as $c>0$, $c\ne1$, so the altered rates stay non-negative. Statement 4 is an equality of rate functions on $\mathcal N_j$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 201, Corollary 9.6

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_PartialBalance_Core
import Definitions.Def_KellyReversibility_PartialBalance_Spatial

namespace KellyReversibility.PartialBalance

open Function KellyStochasticNetworks

/-- **Corollary 9.6** (Kelly 1979, p. 201). For a spatial process with equilibrium distribution
`π`, a site `j` and a constant `c > 0`, `c ≠ 1`, the following are equivalent:
(i) the partial balance equations (9.26) at site `j`;
(ii) for every `n_{G−j}`, the equilibrium distribution of the truncated process at site `j`
with the other sites frozen at `n_{G−j}` is the conditional distribution (9.1);
(iii) the process with every rate `q(n, T_j^m n)` changed to `c q(n, T_j^m n)` has equilibrium
distribution `π`;
(iv) reversing time and freezing the sites other than `j` at `n_{G−j}` commute, for every
`n_{G−j}`. -/
theorem spatial_partial_balance_equivalences {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → Type*} [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (G : SimpleGraph ι) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (hsp : IsSpatialProcess G q)
    (π : (∀ i, N i) → ℝ) (hπ : IsEquilibriumDist q π)
    (j : ι) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≠ 1) :
    List.TFAE
      [ SitePartialBalance π q j,
        ∀ n : (∀ i, N i),
          IsTheEquilibriumDist (frozenRates q j n) (fun a => condProb π j (update n j a)),
        IsTheEquilibriumDist (siteScaled q j c) π,
        ∀ (n : ∀ i, N i) (p : N j → ℝ), IsTheEquilibriumDist (frozenRates q j n) p →
          reversedRates p (frozenRates q j n) = frozenRates (reversedRates π q) j n ] := by sorry

end KellyReversibility.PartialBalance
