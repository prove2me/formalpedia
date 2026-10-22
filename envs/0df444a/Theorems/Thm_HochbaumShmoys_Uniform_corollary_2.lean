-- Prove2me | Theorems.Thm_HochbaumShmoys_Uniform_corollary_2
-- name    : HochbaumShmoys.Uniform.corollary_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:38.513675+00:00
-- url     : https://prove2.me/theorems/bb640f83-4e72-419b-89d1-4795143d4f12
-- title:
--   Corollary 2 — the graph has $O(2m(n/\varepsilon^2)^{(2/\varepsilon^2)+3})$ arcs (p. 547)
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $N\ge2$, $\delta=1/N$, $m\ge1$, $n\ge0$, and let the bins $\beta_1\ge\dots\ge\beta_m>0$ be sorted with $\beta_1=1$; the pieces $\pi_1,\dots,\pi_n$ are arbitrary reals. Then the layered graph of all-pack has at most
--   $$C\cdot 2m\cdot\Big(\frac{n+1}{\delta^2}\Big)^{2/\delta^2+3}=C\cdot 2m\cdot\big((n+1)N^2\big)^{2N^2+3}$$
--   arcs.
--
--   Finding a path from initial to success takes time linear in the number of arcs, so for fixed $\delta$ the procedure all-pack runs in polynomial time.
--
--   **Formalization Note** The $O(\cdot)$ is read with a constant independent of $\delta$ and of the instance; $n$ is replaced by $n+1$. No hypothesis on the piece sizes is needed for the count.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 547, Corollary 2

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph

namespace HochbaumShmoys.Uniform

theorem corollary_2 : ∃ C : ℕ, ∀ (N : ℕ), 2 ≤ N → ∀ (m n : ℕ) (hm : 0 < m)
    (β : Fin m → ℝ) (π : Fin n → ℝ),
    Antitone β → β ⟨0, hm⟩ = 1 → (∀ t, 0 < β t) →
    arcCount N β π ≤ C * (2 * m) * ((n + 1) * N ^ 2) ^ (2 * N ^ 2 + 3) := by sorry

end HochbaumShmoys.Uniform
