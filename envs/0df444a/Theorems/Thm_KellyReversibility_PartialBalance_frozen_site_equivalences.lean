-- Prove2me | Theorems.Thm_KellyReversibility_PartialBalance_frozen_site_equivalences
-- name    : KellyReversibility.PartialBalance.frozen_site_equivalences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:01:20.352869+00:00
-- url     : https://prove2.me/theorems/3dfa08ad-d0cd-497e-bb73-4de5d530d0dd
-- title:
--   Corollary 9.8 — freezing one site at a particular attribute: five equivalent forms of partial balance (9.27)
-- statement:
--   Let $\mathbf n(t)$ be a spatial process over a finite graph $G$ with finite attribute sets, state space $\mathcal S=\prod_j\mathcal N_j$, rates $q$ and equilibrium distribution $\pi$. Fix a site $j$, a particular attribute $a\in\mathcal N_j$, and a constant $c>0$, $c\ne1$, and assume the truncated process $\mathbf n_{G-j}$ obtained by freezing site $j$ at $a$ is irreducible on $\mathcal A=\{\mathbf n:n_j=a\}$. The following statements are equivalent.
--
--   1. $\pi$ satisfies the partial balance equations
--   $$\pi(\mathbf n)\sum_m q(\mathbf n,T_j^m\mathbf n)=\sum_m\pi(T_j^m\mathbf n)q(T_j^m\mathbf n,\mathbf n)\tag{9.27}$$
--   for the particular attribute $n_j=a$ and all values of $\mathbf n_{G-j}$.
--   2. The equilibrium distribution of the truncated process $\mathbf n_{G-j}$ obtained when site $j$ is frozen at $a$ is the conditional distribution $P(\mathbf n_{G-j}\mid n_j=a)=\pi(\mathbf n)/\sum_{\mathbf m:m_j=a}\pi(\mathbf m)$.
--   3. If the rates $q(\mathbf n,T_j^m\mathbf n)$ are changed to $c\,q(\mathbf n,T_j^m\mathbf n)$ for $n_j=a$ and all $\mathbf n_{G-j}$, $m$, the equilibrium distribution of the resulting process is $B\pi(\mathbf n)$ for $n_j=a$ and $Bc\pi(\mathbf n)$ otherwise, with $B^{-1}=\sum_{\mathbf n:n_j=a}\pi(\mathbf n)+c\sum_{\mathbf n:n_j\ne a}\pi(\mathbf n)$.
--   4. Reversing time and freezing site $j$ at $a$ commute.
--
--   If moreover site $j$ has an attribute other than $a$, these are also equivalent to:
--
--   5. The equilibrium distribution of the state just after the attribute of site $j$ has become $a$ equals the equilibrium distribution of the state just before the attribute of site $j$ changes from $a$, as distributions of $\mathbf n$ over $\{\mathbf n:n_j=a\}$.
--
--   **Formalization Note** Truncation to $\{n_j=a\}$ requires irreducibility within that set (p. 25), which is not implied by the spatial-process conditions; it is a hypothesis. Statement 5 is read through the embedded chains of Theorem 9.5 (vi) for $\mathcal A=\{n_j=a\}$; it needs a transition out of $\mathcal A$ to exist, hence the extra attribute. The probability flux out of $\mathcal A$ is finite since the state space is finite.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 202, Corollary 9.8 (proof p. 203)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyReversibility_PartialBalance_Core
import Definitions.Def_KellyReversibility_PartialBalance_ExitEntryChains
import Definitions.Def_KellyReversibility_PartialBalance_Spatial

namespace KellyReversibility.PartialBalance

open Function KellyStochasticNetworks

/-- **Corollary 9.8** (Kelly 1979, p. 202). For a spatial process with equilibrium distribution
`π`, a site `j` frozen at the particular attribute `a` (the truncated process `n_{G−j}` being
irreducible on `{n : n_j = a}`) and a constant `c > 0`, `c ≠ 1`, statements (i)–(iv) are
equivalent; when site `j` has an attribute other than `a`, they are also equivalent to (v). -/
theorem frozen_site_equivalences {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → Type*} [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (G : SimpleGraph ι) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (hsp : IsSpatialProcess G q)
    (π : (∀ i, N i) → ℝ) (hπ : IsEquilibriumDist q π)
    (j : ι) (a : N j) (hAirr : IsIrreducible (truncatedRates q (attrClass j a)))
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≠ 1) :
    List.TFAE
      [ AttrPartialBalance π q j a,
        IsTheEquilibriumDist (truncatedRates q (attrClass j a)) (condDist π (attrClass j a)),
        IsTheEquilibriumDist (attrScaled q j a c) (exitScaledDist π (attrClass j a) c),
        ∀ p : attrClass j a → ℝ, IsTheEquilibriumDist (truncatedRates q (attrClass j a)) p →
          reversedRates p (truncatedRates q (attrClass j a)) =
            truncatedRates (reversedRates π q) (attrClass j a) ] ∧
    ((∃ b : N j, b ≠ a) →
      (AttrPartialBalance π q j a ↔
        ∃ μ : attrClass j a → ℝ, IsTheStationaryDist (entryChain q (attrClass j a)) μ ∧
          IsTheStationaryDist (exitChain q (attrClass j a)) μ)) := by sorry

end KellyReversibility.PartialBalance
