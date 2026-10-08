-- Prove2me | Theorems.Thm_KellyReversibility_MarkovFields_general_spatial_equilibrium
-- name    : KellyReversibility.MarkovFields.general_spatial_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:29:30.53539+00:00
-- url     : https://prove2.me/theorems/88b64bc9-beaa-4ce3-b878-b34ace06ef9c
-- title:
--   Theorem 9.4 — equilibrium distribution $B\prod_j\alpha_j(n_j)/\Phi(\mathbf n)$ of the general spatial process (9.15)
-- statement:
--   Let sites $j$ in a finite set carry attributes from finite nonempty sets $\mathcal N_j$. Let $\Phi(\mathbf n)>0$ and $\Phi_{G-j}(\mathbf n_{G-j})>0$ be positive functions, let $\lambda_j(n,m)\ge 0$, and let $q$ be the transition rates (9.15),
--   $$q(\mathbf n,T_j^m\mathbf n) = \lambda_j(n_j,m)\,\frac{\Phi(\mathbf n)}{\Phi_{G-j}(\mathbf n_{G-j})}.$$
--   Suppose that for each $j$ the functions $\alpha_j>0$ on $\mathcal N_j$ solve
--   $$\alpha_j(n)\sum_{m\in\mathcal N_j}\lambda_j(n,m) = \sum_{m\in\mathcal N_j}\alpha_j(m)\lambda_j(m,n), \qquad n\in\mathcal N_j, \qquad (9.16)$$
--   and that the process is irreducible. Let
--   $$\pi(\mathbf n) = B\,\frac{\prod_{j}\alpha_j(n_j)}{\Phi(\mathbf n)}, \qquad (9.17)$$
--   with $B$ the normalizing constant. Then:
--
--   1. $\pi(\mathbf n)>0$ for every state, and $\sum_{\mathbf n}\pi(\mathbf n)=1$;
--   2. $\pi$ satisfies the partial balance equations, for every site $j$ and state $\mathbf n$,
--   $$\pi(\mathbf n)\sum_{m}q(\mathbf n,T_j^m\mathbf n) = \sum_m \pi(T_j^m\mathbf n)\,q(T_j^m\mathbf n,\mathbf n); \qquad (9.18)$$
--   3. $\pi$ satisfies the equilibrium equations $\pi(\mathbf n)\sum_{\mathbf n'}q(\mathbf n,\mathbf n') = \sum_{\mathbf n'}\pi(\mathbf n')q(\mathbf n',\mathbf n)$;
--   4. $\pi$ is the only positive solution of the equilibrium equations that sums to one.
--
--   So $\pi$ is the equilibrium distribution of the process. The process need not be reversible; when $\Phi$ is a product over the simplices of $G$, (9.17) is a Markov field.
--
--   **Formalization Note** Irreducibility is stated as: every state is reachable from every other by a chain of positive-rate jumps. The equilibrium equations are the published `KellyStochasticNetworks.FullBalance` (an unconditional sum, here over a finite state space). The terms $m=n_j$ in (9.16) and (9.18) cancel ($q(\mathbf n,\mathbf n)=0$ by definition of the rates).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 193 (PDF 196), Theorem 9.4, with Eq. (9.15), (9.16), (9.17), and (9.18) on p. 194 (PDF 197)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_MarkovFields_GeneralSpatialProcess

namespace KellyReversibility.MarkovFields

/-- **Theorem 9.4** (Kelly 1979, p. 193). Let the attribute sets `N j` be finite and nonempty,
let `Φ(n)` and `Φ_{G-j}(n_{G-j})` be positive,
let `λ_j(a, m) ≥ 0`, let `q` be the transition rates (9.15), and let `α_j` be a positive solution
of (9.16), `α_j(a) ∑_m λ_j(a, m) = ∑_m α_j(m) λ_j(m, a)`. Suppose the process is irreducible.
Then `π(n) = B ∏_j α_j(n_j) / Φ(n)` of (9.17), with `B` the normalizing constant, is the
equilibrium distribution: it is positive, sums to one, satisfies the partial balance equations
(9.18) for every site `j` and the equilibrium equations (1.3), and it is the only positive
solution of (1.3) summing to one. -/
theorem general_spatial_equilibrium {V : Type*} [Fintype V] [DecidableEq V]
    {N : V → Type*} [∀ j, Fintype (N j)] [∀ j, Nonempty (N j)] [∀ j, DecidableEq (N j)]
    (lam : (j : V) → N j → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (Φm : (j : V) → ((k : {k : V // k ≠ j}) → N k) → ℝ) (α : (j : V) → N j → ℝ)
    (hlam : ∀ j a m, 0 ≤ lam j a m) (hΦ : ∀ n, 0 < Φ n) (hΦm : ∀ j x, 0 < Φm j x)
    (hα : ∀ j a, 0 < α j a)
    (h916 : ∀ (j : V) (a : N j), α j a * ∑ m : N j, lam j a m = ∑ m : N j, α j m * lam j m a)
    (hirr : ∀ n n' : (k : V) → N k, Relation.ReflTransGen
      (fun a b => 0 < generalSpatialRates lam Φ Φm a b) n n') :
    let q := generalSpatialRates lam Φ Φm
    let π := generalSpatialPi α Φ
    (∀ n, 0 < π n) ∧ (∑ n, π n = 1) ∧
    (∀ (j : V) (n : (k : V) → N k),
      π n * ∑ m : N j, q n (Function.update n j m) =
        ∑ m : N j, π (Function.update n j m) * q (Function.update n j m) n) ∧
    KellyStochasticNetworks.FullBalance π q ∧
    (∀ p : ((j : V) → N j) → ℝ, (∀ n, 0 < p n) → ∑ n, p n = 1 →
      KellyStochasticNetworks.FullBalance p q → p = π) := by sorry

end KellyReversibility.MarkovFields
