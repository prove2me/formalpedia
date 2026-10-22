-- Prove2me | Theorems.Thm_HochbaumShmoys_Uniform_lemma_1
-- name    : HochbaumShmoys.Uniform.lemma_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:28.806991+00:00
-- url     : https://prove2.me/theorems/5e3b721b-c0b2-412b-9086-8d58e8bb6b49
-- title:
--   Lemma 1 — the layered graph has $O(2m\cdot n^{2/\varepsilon^2+3}\cdot 1/\varepsilon^6)$ nodes (p. 546)
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $N\ge2$, $\delta=1/N$, $m\ge1$, $n\ge0$, and let the bins $\beta_1\ge\dots\ge\beta_m>0$ be sorted with $\beta_1=1$ and the pieces satisfy $0<\pi_j\le1$. Then the layered graph of all-pack for this instance has at most
--   $$C\cdot 2m\cdot (n+1)^{2/\delta^2+3}\cdot \frac{1}{\delta^6}=C\cdot 2m\cdot(n+1)^{2N^2+3}\cdot N^6$$
--   nodes.
--
--   For fixed $\delta$ the graph is polynomial in the input size; this is the first step towards the running-time bound of all-pack.
--
--   **Formalization Note** The $O(\cdot)$ is read with a constant independent of $\delta$ and of the instance (quantified before both). $n$ is replaced by $n+1$ so that the bound is meaningful for $n=0$. The node count is that of the graph as defined (one node per state vector in each layer, the first layer holding only the initial node).
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 546, Lemma 1

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph

namespace HochbaumShmoys.Uniform

theorem lemma_1 : ∃ C : ℕ, ∀ (N : ℕ), 2 ≤ N → ∀ (m n : ℕ) (hm : 0 < m)
    (β : Fin m → ℝ) (π : Fin n → ℝ),
    Antitone β → β ⟨0, hm⟩ = 1 → (∀ t, 0 < β t) → (∀ j, 0 < π j ∧ π j ≤ 1) →
    nodeCount N β π ≤ C * (2 * m) * (n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6 := by sorry

end HochbaumShmoys.Uniform
