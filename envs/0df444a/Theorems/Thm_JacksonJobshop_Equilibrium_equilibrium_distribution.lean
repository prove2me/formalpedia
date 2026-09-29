-- Prove2me | Theorems.Thm_JacksonJobshop_Equilibrium_equilibrium_distribution
-- name    : JacksonJobshop.Equilibrium.equilibrium_distribution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:15:25.769158+00:00
-- url     : https://prove2.me/theorems/efe90ec7-80f2-4879-9088-41b322ee83a4
-- title:
--   Theorem (4.5) — if $\pi > 0$, the equilibrium distribution is $p(\bar k) = \pi w(\bar k) W(S(\bar k))$ (uniqueness under bounded arrival rates)
-- statement:
--   Let $(N, L, M, R)$ be a jobshop-like queueing system with $N \ge 1$ service centers satisfying Assumptions (2.1)–(2.4): arrival rates $\lambda(K)$ as in (2.1), service rates $\mu(n, k)$ with $\mu(n, 0) = 0$ and $\mu(n, k) > 0$ for $k \ge 1$, routing probabilities $r(m, n)$ forming a probability distribution in $n \in [1, N+1]$ for each $m \in [0, N]$, and a unique, non-negative solution $e(n)$ of the traffic equations $e(n) = r(0, n) + \sum_{m=1}^N e(m) r(m, n)$. Let
--   $$W(K) = \prod_{i=0}^{K-1}\lambda(i), \qquad w(\bar k) = \prod_{n=1}^N \prod_{i=1}^{k_n} \frac{e(n)}{\mu(n, i)}, \qquad T(K) = \sum_{S(\bar k) = K} w(\bar k),$$
--   and $\pi = \{\sum_{K \ge 0} W(K) T(K)\}^{-1}$ if the sum converges, $\pi = 0$ otherwise.
--
--   **Theorem (4.5).** If $\pi > 0$, then
--   $$p(\bar k) = \pi\, w(\bar k)\, W(S(\bar k)), \qquad \bar k \text{ a state vector}, \tag{4.6}$$
--   is an equilibrium state probability distribution of the system: a probability distribution over state vectors that is a constant solution of the balance equations (3.1). If moreover the arrival rates are bounded, it is the only one.
--
--   The theorem gives the long-run distribution of queue lengths in an open network with state-dependent arrival and service rates in closed product form; the classical Jackson network with Poisson arrivals is its constant-arrival-rate case.
--
--   **Formalization Note** (i) The paper prints $\lambda(S(\bar k))$ as the arrival-outflow coefficient in (3.1); this is inconsistent with its own transition probabilities on p. 134 whenever $r(0, N+1) > 0$, and we use $\lambda(S(\bar k)) \sum_n r(0, n)$, which is the equation those transition probabilities give. (ii) The paper asserts uniqueness without proof, citing a limit theorem for regular processes; we state uniqueness under bounded arrival rates ($\exists \Lambda,\ \forall K,\ \lambda(K) \le \Lambda$), which holds for every example in the paper. Existence and the formula (4.6) carry no extra hypothesis. (iii) An equilibrium is defined from the balance equations for an arbitrary function $q$ on state vectors, never from (4.6).
-- source:
--   Jackson, Jobshop-Like Queueing Systems, Management Science 10(1) (1963), p. 136, Theorem (4.5), eq. (4.6); definitions (3.1) p. 135 and (4.1)-(4.4) p. 136

import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

namespace JacksonJobshop.Equilibrium

/-- Jackson (1963), p. 136, Theorem (4.5): if `π > 0`, then (4.6) `p(k) = π w(k) W(S(k))` is an
equilibrium state probability distribution of System (N, L, M, R) (with (3.1)'s arrival outflow
read as `λ(S(k)) Σ_n r(0, n)`), and, when the arrival rates are bounded, it is the only one. -/
theorem equilibrium_distribution {N : ℕ} (sys : JobshopSystem N) (hπ : 0 < piConst sys) :
    IsEquilibrium sys (productForm sys) ∧
    ((∃ Λ : ℝ, ∀ K, sys.lam K ≤ Λ) →
      ∀ q : (Fin N → ℕ) → ℝ, IsEquilibrium sys q → q = productForm sys) := by sorry

end JacksonJobshop.Equilibrium
