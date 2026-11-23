-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_theorem_3_2_generator_multitape
-- name    : NOFSeparation750.CodedGIP.theorem_3_2_generator_multitape
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:43:39.553808+00:00
-- url     : https://prove2.me/theorems/a8e6bbc8-d7fd-44b3-aada-a7bc878061ec
-- title:
--   Garcia–Stichtenoth codes with a multi-tape generator
-- statement:
--   Fix $k\ge2$ and an allowed $a$, and let $\mathbb F$ be a field of size $4^a$. Write $s=2^a$ and $r_j=(4^a-s)s^j$. There are a family of presented code pairs $V_j,W_j\le\mathbb F^{r_j}$ and a binary representation of $\mathbb F$ such that every pair is $(6/s,3/4)$-compatible for $k$-products, and one deterministic multi-tape machine generates both ordered generator matrices in time polynomial in $r_j$.
--
--   The generator receives $1^j0$ and emits the two matrices in the standard unary-dimension, row-major field-symbol layout. This isolates the algebraic-geometry construction and the Shum–Aleshnikov–Kumar basis computation from the generic matrix-vector encoding step.
-- source:
--   Wang–Wang–Wu, STOC 2027 submission #750, Theorem 3.2 p.7 and Appendix A.2–A.3 pp.12–13, especially the Construction and Computation paragraphs; [GS96, SAK+01].

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_EffectiveCodes
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List

namespace NOFSeparation750.CodedGIP

/-- Appendix A.2--A.3: the compatible second-Garcia--Stichtenoth code family,
with its ordered bases and a polynomial-time multi-tape generator. -/
theorem theorem_3_2_generator_multitape (k a : ℕ) (hk : 2 ≤ k) (ha : Allowed k a)
    (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 4 ^ a) :
    ∃ D : PairFamily F a, ∃ codec : (Fin (2 * a) → Bool) ≃ F,
      (∀ j, Compatible (D j).small.code (D j).large.code k (6 / (2 ^ a : ℝ)) (3 / 4)) ∧
      ∃ (gen : List Bool → List Bool) (tg sg : List Bool → ℕ) (p : Polynomial ℕ),
        Turing.MultiTapeTM.ComputableInTimeAndSpace gen Turing.MultiTapeTM.encBits
          Turing.MultiTapeTM.encBits tg sg ∧
        ∀ j, gen (unary j) = generatorBits codec (D j).small ++ generatorBits codec (D j).large ∧
          tg (unary j) ≤ p.eval (codeLength a j) := by sorry
