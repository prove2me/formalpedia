-- Prove2me | Theorems.Thm_MonotoneDP_Increase_prop12_compactness_convergence
-- name    : MonotoneDP.Increase.prop12_compactness_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:01:34.921062+00:00
-- url     : https://prove2.me/theorems/600b20ce-1e4a-4308-97de-510d6ced5d18
-- title:
--   Proposition 12 — compact U_k(x, λ) give (70), J_∞ = T(J_∞) = T(J*) = J* and an optimal stationary policy
-- statement:
--   Let $(S,C,U,H,\bar J)$ be a monotone model satisfying Assumptions I, I.1 and I.2, and let the control space $C$ be a Hausdorff topological space. Assume there is a nonnegative integer $\bar k$ such that for each $x\in S$, $\lambda\in(-\infty,\infty)$ and $k\ge\bar k$ the set
--
--   $$U_k(x,\lambda)=\{u\in U(x)\mid H[x,u,T^k(\bar J)]\le\lambda\}$$
--
--   is compact. Then
--
--   1. $$P\Bigl(\bigcap_{k=1}^\infty C_k\Bigr)=\bigcap_{k=1}^\infty\overline{P(C_k)};\tag{70}$$
--   2. the dynamic programming algorithm converges to the optimal value function:
--   $$J_\infty=T(J_\infty)=T(J^*)=J^*;$$
--   3. there exists an optimal stationary policy: some $\mu\in M$ has $J_\mu=J^*$.
--
--   This is the paper's sufficient condition for value iteration started at $\bar J$ to converge under the uniform increase assumption, the abstract counterpart of the compactness conditions known for positive-cost deterministic and stochastic control.
--
--   **Formalization Note** The page requires only that $C$ be a topological space; the Hausdorff property is added. The paper's argument uses that accumulation points of a sequence in a compact set lie in that set and Lemma 3, both of which need a separation property (see Lemma 3). Without it the printed proposition is false: take $S=\{0\}$, $C=U(0)=\mathbb N$ with the cofinite topology (every subset is compact), $\bar J(0)=0$ and $H(0,u,J)=J(0)+1/(u+1)$. Then I, I.1 and I.2 (with $\alpha=1$) hold and every $U_k(0,\lambda)$ is compact, but $J^*(0)=0$ is attained by no stationary policy (each gives $+\infty$), and $(0,0)$ lies in $\bigcap_k\overline{P(C_k)}$ but not in $P(\bigcap_k C_k)$, so (70) fails. $\bar k$ is existentially quantified before $x$, $\lambda$ and $k$, as on the page.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), pp. 460–461 (PDF pp. 23–24), Proposition 12, eqs. (69)–(70). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Increase_Epigraph

namespace MonotoneDP.Increase

/-- Bertsekas (1977), pp. 460–461, Proposition 12, with the control space Hausdorff: under I,
I.1 and I.2, if there is `k̄ ∈ ℕ` such that for each `x ∈ S`, `λ ∈ (−∞, ∞)` and `k ≥ k̄` the set
`U_k(x, λ) = {u ∈ U(x) | H[x, u, T^k(J̄)] ≤ λ}` (eq. (69)) is compact, then
`P(⋂_{k≥1} C_k) = ⋂_{k≥1} \overline{P(C_k)}` (eq. (70)), `J_∞ = T(J_∞) = T(J*) = J*`, and there
exists an optimal stationary policy. The page takes `C` to be an arbitrary topological space;
the Hausdorff property is added. -/
theorem prop12_compactness_convergence {S C : Type*} [TopologicalSpace C] [T2Space C]
    (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α)
    (hcpt : ∃ kbar : ℕ, ∀ x : S, ∀ lam : ℝ, ∀ k : ℕ, kbar ≤ k →
      IsCompact {u | u ∈ m.U x ∧ m.H x u ((m.T)^[k] m.Jbar) ≤ (lam : EReal)}) :
    m.P (⋂ k ≥ 1, m.Ck k) = ⋂ k ≥ 1, Pbar (m.P (m.Ck k)) ∧
      (m.Jinf = m.T m.Jinf ∧ m.T m.Jinf = m.T m.Jstar ∧ m.T m.Jstar = m.Jstar) ∧
      ∃ μ : m.Selector, m.Jmu μ = m.Jstar := by sorry

end MonotoneDP.Increase
