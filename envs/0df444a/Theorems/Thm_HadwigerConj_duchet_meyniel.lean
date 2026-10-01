-- Prove2me | Theorems.Thm_HadwigerConj_duchet_meyniel
-- name    : HadwigerConj.duchet_meyniel
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T00:08:35.03008+00:00
-- url     : https://prove2.me/theorems/c08dc1c2-4c99-477b-b5e8-98fe131a1e28
-- title:
--   Theorem 4.1 (Duchet–Meyniel): a $K_t$ minor with $t\ge n/(2\alpha(G)-1)$
-- statement:
--   Every finite graph $G$ with $n$ vertices and stability number $\alpha(G)$ (the largest size of a set of pairwise non-adjacent vertices) has a $K_t$ minor with
--
--   $$t\ \ge\ \frac{n}{2\alpha(G)-1}.$$
--
--   Since $\chi(G)\ge n/\alpha(G)$, Hadwiger's conjecture would give a clique minor of size $\lceil n/\alpha(G)\rceil$; this theorem is within a factor of $2$ of that.
--
--   **Formalization Note** The quotient is computed in the reals. For $n=0$ it equals $0$.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Theorem 4.1 (p. 7)

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem duchet_meyniel {V : Type} [Finite V] (G : SimpleGraph V) :
    ∃ t : ℕ, HasCompleteMinor G t ∧
      (Nat.card V : ℝ) / (2 * (G.indepNum : ℝ) - 1) ≤ t := by sorry
end HadwigerConj
