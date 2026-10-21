-- Prove2me | Theorems.Thm_HochbaumShmoys_Uniform_lemma_2
-- name    : HochbaumShmoys.Uniform.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:45.010564+00:00
-- url     : https://prove2.me/theorems/8a3580f3-398b-4886-92ba-14dc4ae87948
-- title:
--   Lemma 2 — $O((1/\varepsilon^2)^{2/\varepsilon^2})$ arcs leave each node (p. 547)
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $N\ge2$, $\delta=1/N$, $m\ge1$, $n\ge0$, let the bins $\beta_1\ge\dots\ge\beta_m>0$ be sorted with $\beta_1=1$, and let $0<\pi_j\le 1$. Then every node $v$ of the layered graph of all-pack (indeed every element of the node type) has at most
--   $$C\cdot\Big(\frac{1}{\delta^2}\Big)^{2/\delta^2}=C\cdot (N^2)^{2N^2}$$
--   distinct successors.
--
--   The out-degree is bounded independently of $m$ and $n$, so the number of arcs is at most a constant (depending on $\delta$) times the number of nodes.
--
--   **Formalization Note** The $O(\cdot)$ is read with a constant independent of $\delta$ and of the instance. Arcs are counted as distinct heads of the arc relation.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 547, Lemma 2

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph

namespace HochbaumShmoys.Uniform

theorem lemma_2 : ∃ C : ℕ, ∀ (N : ℕ), 2 ≤ N → ∀ (m n : ℕ) (hm : 0 < m)
    (β : Fin m → ℝ) (π : Fin n → ℝ),
    Antitone β → β ⟨0, hm⟩ = 1 → (∀ t, 0 < β t) → (∀ j, 0 < π j ∧ π j ≤ 1) →
    ∀ v : Node m N n,
      Nat.card {w : Node m N n // Arc N β π v w} ≤ C * (N ^ 2) ^ (2 * N ^ 2) := by sorry

end HochbaumShmoys.Uniform
