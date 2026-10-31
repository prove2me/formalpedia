-- Prove2me | Theorems.Thm_MNatOps_Monotone_thm3_induction
-- name    : MNatOps.Monotone.thm3_induction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:11.200404+00:00
-- url     : https://prove2.me/theorems/7358f626-ce12-4bfc-9b12-8e206db117d6
-- title:
--   Proof of Theorem 3, p. 11 — induction claim: A*_B(s′) ∩ I_{≤,i}(a) ≠ ∅ for i = 0, …, n
-- statement:
--   Let $G : \mathbb Z^m \times \mathbb Z^n \to \mathbb R \cup \{-\infty\}$ be SSQM♮-concave, let $B = [l, u] \cap \mathbb Z^n$ be a box, and let $s \le s'$ be parameters. Assume that problem (3) at $s'$ has an optimal solution with finite value, and let $a \in \mathcal A^*_B(s)$ with $G(s, a) > -\infty$. Then for every $i = 0, 1, \dots, n$,
--   $$
--   \mathcal A^*_B(s') \cap I_{\le, i}(a) \neq \emptyset, \qquad I_{\le, i}(a) = \{a'' : a''_k \le a_k,\ k = 1, \dots, i\}.
--   $$
--
--   This is the claim proved by induction on $i$ in the proof of Theorem 3; the case $i = n$ is the first half of the theorem.
--
--   **Formalization Note** $I_{\le, i}(a)$ is `lowerOrthant a i`, which constrains the `Fin n` indices with value $< i$. The finite-value hypothesis on $s'$ is the mission's standing restriction of the parameter set (see Theorem 3).
-- source:
--   Chen & Li, M♮-Convexity and Its Applications in Operations, SSRN 3431474 (PDF sha256 ea81b5d5…), p. 11, proof of Theorem 3, 'We show by induction that A*_B(s′) ∩ I≤,i(a) ≠ ∅ for i = 0, ..., n.'

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model

namespace MNatOps.Monotone

theorem thm3_induction {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (hG : SSQMNatConcave G)
    (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (s s' : Fin m → ℤ) (hss : s ≤ s')
    (a : Fin n → ℤ) (ha : a ∈ optSet G l u s) (haf : G (Sum.elim s a) ≠ ⊥)
    (hs' : s' ∈ finiteParams G l u) :
    ∀ r : ℕ, r ≤ n → ∃ a'' ∈ optSet G l u s', a'' ∈ lowerOrthant a r := by sorry

end MNatOps.Monotone
