-- Prove2me | Theorems.Thm_MNatOps_Monotone_thm3_second_half
-- name    : MNatOps.Monotone.thm3_second_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:25.124913+00:00
-- url     : https://prove2.me/theorems/dcde9fe7-8535-42c5-9e27-bc493bfce57e
-- title:
--   Proof of Theorem 3, p. 11 — second half: for a′ ∈ A*_B(s′) some a ∈ A*_B(s) satisfies a ≥ a′
-- statement:
--   Let $G : \mathbb Z^m \times \mathbb Z^n \to \mathbb R \cup \{-\infty\}$ be SSQM♮-concave, let $B = [l, u] \cap \mathbb Z^n$ be a box, and let $s \le s'$ be parameters. Assume that problem (3) at $s$ has an optimal solution with finite value, and let $a' \in \mathcal A^*_B(s')$ with $G(s', a') > -\infty$. Then there exists
--   $$
--   a \in \mathcal A^*_B(s) \quad\text{with}\quad a \ge a' .
--   $$
--
--   This is the second half of the weak induced set ordering asserted by Theorem 3; the paper obtains it by "the same argument" as the first half.
--
--   **Formalization Note** The order on $\mathbb Z^n$ is componentwise. The finite-value hypotheses are the mission's standing restriction of the parameter set (see Theorem 3).
-- source:
--   Chen & Li, M♮-Convexity and Its Applications in Operations, SSRN 3431474 (PDF sha256 ea81b5d5…), p. 11, proof of Theorem 3, 'For any a′ ∈ A*_B(s′), we can follow the same argument to prove that there exists a ∈ A*_B(s) with a ≥ a′.'

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model

namespace MNatOps.Monotone

theorem thm3_second_half {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (hG : SSQMNatConcave G)
    (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (s s' : Fin m → ℤ) (hss : s ≤ s')
    (hs : s ∈ finiteParams G l u)
    (a' : Fin n → ℤ) (ha' : a' ∈ optSet G l u s') (ha'f : G (Sum.elim s' a') ≠ ⊥) :
    ∃ a ∈ optSet G l u s, a' ≤ a := by sorry

end MNatOps.Monotone
