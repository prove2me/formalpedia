-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_constant_user_total
-- name    : MusicStreaming.Axioms.constant_user_total
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:31.919835+00:00
-- url     : https://prove2.me/theorems/17ea7821-54f8-4464-832f-b1b2ca557628
-- title:
--   Appendix, proof of Theorem 1(c), p. 20 — under equal global impact Σᵢ Iᵢ(N, {j}, t.j) does not depend on j and t.j
-- statement:
--   Let $I$ be an index satisfying equal global impact of users. Then for all users $j,j'$ and all nonzero profiles $x,y\in\mathbb N^N$,
--   $$\sum_{i\in N}I_i(N,\{j\},x)=\sum_{i\in N}I_i(N,\{j'\},y).$$
--
--   The paper derives this from the two-user problem $M^*=\{j,j'\}$. Writing $\lambda$ for the common value and combining with the one-user form gives $I_i=\sum_{j\in M}\frac{\lambda}{T^j}t_{ij}=\lambda U_i$, the "only if" direction of Theorem 1(c).
--
--   **Formalization Note** Only equal global impact is assumed. The statement includes $j=j'$ with $x\neq y$, which the two-user argument reaches through a third user; user names range over all natural numbers.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 20, Appendix, proof of Theorem 1(c), from "Let j, j′ ∈ M and M* = {j, j′}" to "λ = Σ_{i∈N} I_i(N, {j}, t.j)"

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Axioms

theorem constant_user_total {n : ℕ} (I : Index n) (hG : EqualGlobalImpact I) :
    ∀ (j j' : ℕ) (x y : Fin n → ℕ), x ≠ 0 → y ≠ 0 →
      ∑ i, I (Finsupp.single j x) i = ∑ i, I (Finsupp.single j' y) i := by sorry

end MusicStreaming.Axioms
