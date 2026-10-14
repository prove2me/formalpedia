-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_6_4
-- name    : OAI.FiniteAlgebraicEnvelopes.lemma_6_4
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-14T09:44:43.526535+00:00
-- url     : https://prove2.me/theorems/d04b9ea4-2a24-4ad0-ba84-4092688e9480
-- title:
--   Lemma 6.4 (two equivalent subcorners in $k[P]$)
-- statement:
--   **Lemma 6.4** of OpenAI's "Finite algebraic envelopes and the Boone-Higman conjecture" preprint (Section 6.3, just before Theorem 2.2's proof). Working in the group algebra $k[P] = \mathbb{F}_2[P]$ of Lemma 6.1's monoid $P$ of partial affine maps of $\mathbb{Q}$, there is a nonzero idempotent $q \in k[P]$ (so $q^2 = q$, $q \neq 0$, $q \neq 1$) together with four elements $s_0, s_1, t_0, t_1$ of the corner algebra $qk[P]q$ satisfying $t_i s_j = \delta_{ij} q$ and $s_0 t_0 + s_1 t_1 = q$. Concretely, $q = e_0 - e_1$ for the partial identities $e_a$ on $[a, \infty) \cap \mathbb{Q}$, which decomposes as $q = q_0 + q_1$ for the two orthogonal idempotents $q_0 = u e_0 u^{-1} = e_0 - e_{1/2}$ and $q_1 = v e_0 v^{-1}$ (wait: $q_1 = v q v^{-1} = e_{1/2} - e_1$), where $u(x) = x/2$ and $v(x) = (x+1)/2$ are the two generators of $P$; then $s_j = w_j q$ and $t_j = q w_j^{-1}$ for $w_0 = u, w_1 = v$. This supplies the 'two equivalent subcorners' splitting data that Theorem 2.2's proof (Section 6.3-6.4) uses to build the self-embedding $\varphi : B \to B$ and the binary splitting pairs $s_0, s_1, t_0, t_1 \in pBp$ of equation (28).
-- source:
--   OpenAI, "Finite algebraic envelopes and the Boone-Higman conjecture", OpenAI Math Release, 2026-09-23, Section 6.3, Lemma 6.4.

import Mathlib
import Definitions.Def_BooneHigman_PMonoid

open OAI.FiniteAlgebraicEnvelopes
open OAI.FiniteAlgebraicEnvelopes.PElem

theorem OAI.FiniteAlgebraicEnvelopes.lemma_6_4 :
    ∃ q : MonoidAlgebra (ZMod 2) PElem, q * q = q ∧ q ≠ 0 ∧ q ≠ 1 ∧
      ∃ s0 s1 t0 t1 : MonoidAlgebra (ZMod 2) PElem,
        q * s0 * q = s0 ∧ q * s1 * q = s1 ∧ q * t0 * q = t0 ∧ q * t1 * q = t1 ∧
        t0 * s0 = q ∧ t1 * s1 = q ∧ t0 * s1 = 0 ∧ t1 * s0 = 0 ∧
        s0 * t0 + s1 * t1 = q := by sorry
