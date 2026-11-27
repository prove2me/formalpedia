-- Prove2me | Theorems.Thm_NadlerCLS_mem_P_of_bits
-- name    : NadlerCLS.mem_P_of_bits
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:24:30.233344+00:00
-- url     : https://prove2.me/theorems/db72f104-06f9-42eb-822d-c791ceeddc79
-- title:
--   A language decided by a polynomial-time binary checker is in P
-- statement:
--   Let $L$ be a language over the pair alphabet $\Sigma=\{\#\}\cup\{0_A,1_A,0_B,1_B\}$ and let $\mathrm{bin}:\Sigma^*\to\{0,1\}^*$ be the letterwise binary code $\#\mapsto 0$, $b_A\mapsto 10b$, $b_B\mapsto 11b$. Suppose $\chi:\{0,1\}^*\to\{0,1\}^*$ is computable in polynomial time and decides $L$ through this code:
--
--   $$x\in L\iff \chi(\mathrm{bin}(x))=1\qquad\text{for every }x\in\Sigma^* .$$
--
--   Then $L\in\mathrm{P}$.
--
--   This turns a polynomial-time binary checker into membership of a checking language $L_R=\{w\#y : R(w,y)\}$ in $\mathrm P$, the verification condition of TFNP.
--
--   **Formalization Note** $\mathrm P$ and polynomial time are Cook's `CookPvsNP.P` and `CookPvsNP.PolyTimeComputable` (one-tape machines); the one-bit word $1$ is `[true]`.
-- source:
--   Formalization infrastructure for the TFNP verification condition used for CLS-membership in Xiong–Vlatakis-Gkaragkounis, arXiv:2609.14101v4, Section 3, p.9 ("An output of type (N2) can be checked in polynomial time") and Theorem 3.2, p.11; class P and reductions as in S. Cook, The P versus NP problem, §1 and Proposition 1(a).

import Mathlib
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace NadlerCLS

theorem mem_P_of_bits (L : CookPvsNP.Lang (Option (Bool ⊕ Bool))) (χ : List Bool → List Bool)
    (hχ : CookPvsNP.PolyTimeComputable χ)
    (hL : ∀ x, x ∈ L ↔ χ (x.flatMap (fun c => match c with
      | none => [false]
      | some (Sum.inl b) => [true, false, b]
      | some (Sum.inr b) => [true, true, b])) = [true]) :
    L ∈ CookPvsNP.P (Option (Bool ⊕ Bool)) := by sorry

end NadlerCLS
