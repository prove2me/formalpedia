-- Prove2me | Theorems.Thm_MNatOps_Monotone_theorem_3
-- name    : MNatOps.Monotone.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:20.356874+00:00
-- url     : https://prove2.me/theorems/529c8d30-b605-4849-befe-fbdce64a07b0
-- title:
--   Theorem 3, p. 10 — for SSQM♮-concave G on Zᵐ × Zⁿ and a box B, the optimal-solution set A*_B(s) is nonincreasing in s (finite optimal values)
-- statement:
--   Let $G : \mathbb Z^m \times \mathbb Z^n \to \mathbb R \cup \{-\infty\}$ be SSQM♮-concave in the joint variable $(s, a)$, and let $B = [l, u] \cap \mathbb Z^n$ be a box with $l \in (\mathbb Z \cup \{-\infty\})^n$, $u \in (\mathbb Z \cup \{+\infty\})^n$ and $l \le u$. For a parameter $s \in \mathbb Z^m$ let $\mathcal A^*_B(s)$ be the set of optimal solutions of
--   $$
--   \max\ G(s, a) \quad \text{s.t. } a \in B, \tag{3}
--   $$
--   and let $S$ be the set of parameters $s$ for which (3) has an optimal solution with finite value $G(s, a) > -\infty$. Then $\mathcal A^*_B(s)$ is nonincreasing in $s \in S$: for all $s, s' \in S$ with $s \le s'$,
--
--   1. for every $a \in \mathcal A^*_B(s)$ there is $a' \in \mathcal A^*_B(s')$ with $a' \le a$, and
--   2. for every $a' \in \mathcal A^*_B(s')$ there is $a \in \mathcal A^*_B(s)$ with $a' \le a$.
--
--   This is the paper's general tool for substitutable problems: where lattice programming (Topkis) gives optimal solutions that *increase* in the parameters under complementarity, SSQM♮-concavity gives optimal solutions that *decrease*, in the weak induced set ordering.
--
--   **Formalization Note** Two deliberate deviations from the page. (i) Only the integer case $\mathcal F = \mathbb Z$ is formalized; there Assumption (⋆) (upper semicontinuity) holds automatically, as the paper notes, and it does not appear. (ii) The paper takes $S = \{s : \mathcal A^*_B(s) \neq \emptyset\}$. With that $S$ the statement is false when an optimal value is $-\infty$: for $m = n = 1$, $B = [0, 1]$ and $G(s, a) = a$ if $s = 1$, $-\infty$ otherwise, $G$ is SSQM♮-concave, $\mathcal A^*_B(0) = \{0, 1\}$ and $\mathcal A^*_B(1) = \{1\}$, so $0 \in \mathcal A^*_B(0)$ has no smaller element in $\mathcal A^*_B(1)$. The formal $S$ is therefore the set of parameters with a finite optimal value, which is exactly what the paper's proof uses (it applies Definition 1 at optimal points, which must lie in $\operatorname{dom} G$). The hypothesis $l \le u$ is kept for fidelity.
-- source:
--   Chen & Li, M♮-Convexity and Its Applications in Operations, SSRN 3431474 (PDF sha256 ea81b5d5…), p. 10, Theorem 3

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model

namespace MNatOps.Monotone

theorem theorem_3 {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (hG : SSQMNatConcave G)
    (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (hlu : BoxNonempty l u) :
    IsNonincreasingOn (optSet G l u) (finiteParams G l u) := by sorry

end MNatOps.Monotone
