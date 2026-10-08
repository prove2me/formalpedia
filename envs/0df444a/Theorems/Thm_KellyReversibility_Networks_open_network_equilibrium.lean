-- Prove2me | Theorems.Thm_KellyReversibility_Networks_open_network_equilibrium
-- name    : KellyReversibility.Networks.open_network_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:52:17.540299+00:00
-- url     : https://prove2.me/theorems/c812840c-7d4a-41c0-93c5-4864d4c3bd80
-- title:
--   Theorem 3.1 — the open network of §3.1 has equilibrium distribution $\pi(\mathbf C)=\prod_j\pi_j(\mathbf c_j)$
-- statement:
--   Consider an open network of $J$ queues with $I$ customer types as in Section 3.1: type-$i$ customers arrive in a Poisson stream of rate $\nu(i)>0$ and follow the route $r(i,1),\dots,r(i,S(i))$ (no two successive stages at the same queue); queue $j$ supplies service effort $\phi_j(n_j)>0$ when it holds $n_j>0$ customers, a proportion $\gamma_j(l,n_j)$ of it to position $l$, and an arriving customer takes position $l$ with probability $\delta_j(l,n_j+1)$. Let $q$ be the transition rates (3.2), (3.4), (3.6) of the state $\mathbf C=(\mathbf c_1,\dots,\mathbf c_J)$, and let $\alpha_j(i,s)$, $a_j$, $b_j$, $\pi_j$ be as on p. 61. Assume none of $b_1,\dots,b_J$ is zero, i.e. every series
--   $$b_j^{-1}=\sum_{n=0}^{\infty}\frac{a_j^n}{\prod_{l=1}^{n}\phi_j(l)}$$
--   converges. Then
--   $$\pi(\mathbf C)=\prod_{j=1}^{J}\pi_j(\mathbf c_j)$$
--   is the equilibrium distribution of the network: $\pi(\mathbf C)>0$ for every state $\mathbf C$, $\sum_{\mathbf C}\pi(\mathbf C)=1$, and for every state $\mathbf C$
--   $$\pi(\mathbf C)\sum_{\mathbf D}q(\mathbf C,\mathbf D)=\sum_{\mathbf D}\pi(\mathbf D)\,q(\mathbf D,\mathbf C).$$
--
--   This is the product-form theorem for networks in which the route of a customer is determined by his type, so that a customer's future route may depend on his past route; it parallels Theorem 2.4 for open migration processes.
--
--   **Formalization Note** The equilibrium property is stated as positivity, normalization over all network states (`HasSum`) and the equilibrium equations (published `KellyStochasticNetworks.FullBalance`). That a Markov process with these rates exists, is irreducible and non-explosive, and has $\pi$ as its unique stationary law is not formalized. Types and queues are finite (`Fin I`, `Fin J`).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 61, Theorem 3.1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Networks_OpenNetwork
import Definitions.Def_KellyReversibility_Networks_ProductForm

namespace KellyReversibility.Networks

/-- **Theorem 3.1** (Kelly 1979, p. 61). For an open network of queues with general customer
routes satisfying the constraints of §3.1, if every series `b_j⁻¹ = ∑_n a_j^n / ∏_{l ≤ n} φ_j(l)`
converges, then `π(C) = ∏_j π_j(c_j)` is the equilibrium distribution: it is positive, sums to `1`
over all network states, and satisfies the equilibrium equations for the rates (3.2), (3.4), (3.6). -/
theorem open_network_equilibrium {I J : ℕ} (N : Network I J) (hN : N.IsValid)
    (hb : ∀ j : Fin J, Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n)) :
    (∀ C : N.State, 0 < N.netPi C) ∧ HasSum N.netPi 1 ∧
      KellyStochasticNetworks.FullBalance N.netPi N.rate := by sorry

end KellyReversibility.Networks
