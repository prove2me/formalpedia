-- Prove2me | Theorems.Thm_KellyReversibility_Networks_reversed_network
-- name    : KellyReversibility.Networks.reversed_network
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:52:05.254516+00:00
-- url     : https://prove2.me/theorems/11869128-30b8-4738-ae73-5ad3e6d2ac5c
-- title:
--   Theorem 3.2 — the reversed open network is an open network of the same form
-- statement:
--   Let an open network of queues with general customer routes (Section 3.1) satisfy the book's constraints, and assume that every series $b_j^{-1}=\sum_{n\ge0}a_j^n/\prod_{l=1}^{n}\phi_j(l)$ converges. Let $\pi(\mathbf C)=\prod_j\pi_j(\mathbf c_j)$ be the product form of Theorem 3.1 and $q$ the transition rates (3.2), (3.4), (3.6). Then for all states $\mathbf C,\mathbf D$,
--   $$\frac{\pi(\mathbf D)\,q(\mathbf D,\mathbf C)}{\pi(\mathbf C)}=\tilde q(\tilde{\mathbf C},\tilde{\mathbf D}),$$
--   where $\tilde q$ are the transition rates of the **reversed network** — the same arrival rates $\nu(i)$ and effort functions $\phi_j$, each route traversed in the opposite order $r(i,S(i)),\dots,r(i,1)$, and the functions $\gamma_j$ and $\delta_j$ interchanged — and $\tilde{\mathbf C}$ is $\mathbf C$ with each customer's stage counted from the other end of his route.
--
--   The left-hand side is the transition rate of the time-reversed stationary process, so the reversed process $\mathbf C(-t)$ is again an open network of queues of the form of Section 3.1. Together with equal total exit rates this identity is what gives Theorem 3.1.
--
--   **Formalization Note** This is the rate-level content of Theorem 3.2: the reversed process is identified through its transition rates $\pi(\mathbf D)q(\mathbf D,\mathbf C)/\pi(\mathbf C)$ (published `KellyStochasticNetworks.reversedRates`). That $\pi$ is the stationary law of a Markov process with these rates, and the process-level construction of $\mathbf C(-t)$, are not formalized. Types and queues are finite.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 62, Theorem 3.2 (reversed rates q' displayed on p. 62)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Networks_OpenNetwork
import Definitions.Def_KellyReversibility_Networks_ProductForm

namespace KellyReversibility.Networks

/-- **Theorem 3.2** (Kelly 1979, p. 62), rate-level reading. The transition rates of the time
reversal of the stationary network, `q'(C, D) = π(D) q(D, C) / π(C)` with `π` the product form of
Theorem 3.1, are exactly the transition rates (3.2), (3.4), (3.6) of the reversed network
`N.reverse` (routes traversed backwards, `γ_j` and `δ_j` interchanged), read on the relabelled
states. -/
theorem reversed_network {I J : ℕ} (N : Network I J) (hN : N.IsValid)
    (hb : ∀ j : Fin J, Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n)) :
    ∀ C D : N.State,
      KellyStochasticNetworks.reversedRates N.netPi N.rate C D =
        N.reverse.rate (N.revState C) (N.revState D) := by sorry

end KellyReversibility.Networks
