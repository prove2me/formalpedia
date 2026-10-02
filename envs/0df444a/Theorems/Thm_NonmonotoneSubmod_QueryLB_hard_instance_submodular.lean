-- Prove2me | Theorems.Thm_NonmonotoneSubmod_QueryLB_hard_instance_submodular
-- name    : NonmonotoneSubmod.QueryLB.hard_instance_submodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:15:10.177991+00:00
-- url     : https://prove2.me/theorems/aa9bff90-4b24-47a7-ac18-21a0801a8a9f
-- title:
--   §4.2 — the hard instance $f_C$ is submodular
-- statement:
--   Let $n$ be even and $m$ an integer with $1 \le m$ and $2m \le n$ (so $\epsilon = m/n \in (0, \tfrac12]$ and $\epsilon n$ is an integer). For every $C \subseteq [n]$ with $|C| = n/2$, the hard instance $f_C(S) = f(|S \cap C|, |S \setminus C|)$ of Theorem 4.5 satisfies
--
--   $$
--   f_C(S \cup T) + f_C(S \cap T) \le f_C(S) + f_C(T) \qquad \text{for all } S, T \subseteq [n].
--   $$
--
--   Submodularity is what makes $\{f_C\}$ a legitimate family of instances for the lower bound.
--
--   **Formalization Note** $\epsilon n$ is the integer $m$, following the paper's "assume that $\epsilon n$ is an integer"; $n$ even and $|C| = n/2$ are the paper's $|C| = |D| = n/2$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1150, §4.2, proof of Theorem 4.5, last paragraph (marginal values of f(k, ℓ))

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance

namespace NonmonotoneSubmod.QueryLB

/-- §4.2, proof of Theorem 4.5 (p. 1150, last paragraph): for `n` even, `1 ≤ m`, `2m ≤ n`
(`ϵ = m/n ∈ (0, 1/2]`) and every `C ⊆ [n]` with `|C| = n/2`, the function
`f_C(S) = f(|S ∩ C|, |S ∖ C|)` is submodular. -/
theorem hard_instance_submodular (n m : ℕ) (hn : Even n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (C : Finset (Fin n)) (hC : C.card = n / 2) :
    NonmonotoneSubmod.Shared.Submodular (fC n m C) := by sorry

end NonmonotoneSubmod.QueryLB
