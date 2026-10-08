-- Prove2me | Theorems.Thm_KellyReversibility_Networks_arrival_sees_equilibrium
-- name    : KellyReversibility.Networks.arrival_sees_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:52:15.755577+00:00
-- url     : https://prove2.me/theorems/5d4e4a1d-7568-4bf4-913e-222aaf9e6279
-- title:
--   Corollary 3.5 — a type-$i$ customer reaching queue $j$ finds it in state $\mathbf c_j$ with probability $\pi_j(\mathbf c_j)$
-- statement:
--   Let an open network of queues with general customer routes (Section 3.1) satisfy the book's constraints, assume every series $b_j^{-1}=\sum_{n\ge0}a_j^n/\prod_{l=1}^n\phi_j(l)$ converges, and let $\pi$ be the equilibrium distribution of Theorem 3.1. Fix a type $i$ and a stage $s$ of its route, and let $j=r(i,s)$. Write $A_{i,s}(\mathbf C)$ for the total probability intensity, in state $\mathbf C$, that a type-$i$ customer reaches queue $j$ at stage $s$ of his route (by entering the system if $s=1$, by completing service at queue $r(i,s-1)$ at stage $s-1$ if $s>1$). Then
--   $$\sum_{\mathbf C}\pi(\mathbf C)A_{i,s}(\mathbf C)=\nu(i),\qquad \sum_{\mathbf C:\,\mathbf c_j=\mathbf c}\pi(\mathbf C)A_{i,s}(\mathbf C)=\nu(i)\,\pi_j(\mathbf c),$$
--   and
--   $$\sum_{\mathbf C:\,n_j=n}\pi(\mathbf C)A_{i,s}(\mathbf C)=\nu(i)\,b_j\frac{a_j^n}{\prod_{l=1}^{n}\phi_j(l)}.$$
--   Dividing by the total flux $\nu(i)$: when a customer of type $i$ reaches queue $j$ at stage $s$ of his route, the probability that he finds queue $j$ in state $\mathbf c_j$ is $\pi_j(\mathbf c_j)$, and the probability that he finds $n$ customers there is given by (3.7).
--
--   **Formalization Note** "The probability that he finds queue $j$ in state $\mathbf c_j$" is read as a ratio of equilibrium probability fluxes: the flux of stage-$s$ type-$i$ arrivals at queue $j$ that occur from states with $\mathbf c_j=\mathbf c$, divided by the total flux of such arrivals. The state found is the state just before the arrival. Types and queues are finite.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 63, Corollary 3.5 (and the flux identity in its proof)

import Mathlib
import Definitions.Def_KellyReversibility_Networks_OpenNetwork
import Definitions.Def_KellyReversibility_Networks_ProductForm

namespace KellyReversibility.Networks

/-- **Corollary 3.5** (Kelly 1979, p. 63), as a statement about arrival fluxes. Under the
product-form equilibrium `π` of Theorem 3.1, let `j = r(i, s)`. The total equilibrium flux of
type-`i` customers reaching queue `j` at stage `s` of their route is `ν(i)`; the flux of those that
find queue `j` in state `c` is `ν(i) π_j(c)`; and the flux of those that find `n` customers in
queue `j` is `ν(i)` times the probability (3.7). -/
theorem arrival_sees_equilibrium {I J : ℕ} (N : Network I J) (hN : N.IsValid)
    (hb : ∀ j : Fin J, Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n))
    (i : Fin I) (s : Fin (N.S i)) :
    HasSum (fun C : N.State => N.netPi C * N.arrivalIntensity i s C) (N.ν i) ∧
    (∀ c : List (N.Cls (N.r i s)),
      HasSum (fun C : {C : N.State // C (N.r i s) = c} =>
        N.netPi C * N.arrivalIntensity i s C) (N.ν i * N.queuePi (N.r i s) c)) ∧
    (∀ n : ℕ,
      HasSum (fun C : {C : N.State // (C (N.r i s)).length = n} =>
        N.netPi C * N.arrivalIntensity i s C)
        (N.ν i * (N.b (N.r i s) * N.a (N.r i s) ^ n / N.phiProd (N.r i s) n))) := by sorry

end KellyReversibility.Networks
