-- Prove2me | Theorems.Thm_NetPriceDisc_Random_theorem_5_1
-- name    : NetPriceDisc.Random.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:00.916261+00:00
-- url     : https://prove2.me/theorems/f455a493-6cf6-4b1a-be0c-dc3c49aea1da
-- title:
--   Theorem 5.1, p. 12 — for any density sequence, E[R(p₀)] = o(n) and E[R_F(p₀)] = o(1) in directed Erdős–Rényi networks
-- statement:
--   Fix $a>0$, a marginal cost $c<a$ and a network coefficient $\rho\in(0,1)$. For each $n$, let $G$ be the directed Erdős–Rényi network $G(n,p(n))$ on $n$ consumers, and let $R(p_0)$ and $R_F(p_0)$ be the regret and fractional regret of the uniform price $p_0=\frac{a+c}2\mathbf 1$. For **every** sequence of densities $(p(n))_{n\in\mathbb N}$ in $[0,1]$,
--   $$\mathbb E_G[R(p_0)]=o(n)\qquad\text{and}\qquad\mathbb E_G[R_F(p_0)]=o(1)\qquad(n\to\infty).$$
--
--   This is the main result of the paper on random networks: whatever the density of the network, a seller who ignores the network and charges one price loses a vanishing fraction of the profit a fully discriminating seller earns.
--
--   **Formalization Note.** $o(n)$ is `Asymptotics.IsLittleO` at `atTop` against $n\mapsto n$, and $o(1)$ is convergence to $0$. The fractional regret is the expectation of the ratio $1-\pi(p_0)/\pi^*$, as in the paper's proof (p. 40), not a ratio of expectations. No restriction on the density sequence is imposed. The expectation is the finite sum over arc sets of the Model file.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 12, Theorem 5.1 (proof pp. 36–39, App. D.1)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem theorem_5_1 (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1) :
    (fun n : ℕ => erExpect n (p n) (regret a c ρ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) ∧
      Filter.Tendsto (fun n : ℕ => erExpect n (p n) (fracRegret a c ρ)) Filter.atTop (nhds 0) := by sorry

end NetPriceDisc.Random
