-- Prove2me | Theorems.Thm_InteractionElim_Main_lemma_A_3
-- name    : InteractionElim.Main.lemma_A_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:20:23.369165+00:00
-- url     : https://prove2.me/theorems/8d278a30-d53b-4b0f-a0b6-4f1cd7712855
-- title:
--   Lemma A.3 — $\max\{1,c\sqrt r\}\le F(W)\le G(W)\le r$, $F_r\le C\sqrt{r\log_2(r+1)}$, $G(\mathbb F_2^r)\asymp\sqrt{r\log_2(r+1)}$, $F_1=1$
-- statement:
--   There are universal constants $c,C>0$ such that for every $r\ge1$ and every subspace $W\le\mathbb F_2^r$,
--   $$
--   \max\{1,c\sqrt r\}\le F(W)\le G(W)\le r, \tag{A.7}
--   $$
--   and, writing $F_r=F(\mathbb F_2^r)$,
--   $$
--   F_r\le C\sqrt{r\log_2(r+1)},\qquad c\sqrt{r\log_2(r+1)}\le G(\mathbb F_2^r)\le C\sqrt{r\log_2(r+1)},\qquad F_1=1. \tag{A.8}
--   $$
--   These universal geometric bounds absorb the price of covers and of proposing candidates, and allow comparisons without solving the finite optimizations.
--
--   Differences from the source:
--   - encoding: universal constants, O(·) and ≍ → explicit existentially quantified positive real constants, quantified before every instance-dependent object; reason: the notation convention of p. 4: a ≍ b means two inequalities with positive universal constants
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 18, Lemma A.3, Eqs. (A.7)-(A.8)

import Mathlib
import Definitions.Def_InteractionElim_Main_Certificate

open scoped BigOperators

namespace InteractionElim.Main

theorem lemma_A_3 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ r : ℕ, 1 ≤ r → ∀ W : Submodule (ZMod 2) (Fin r → ZMod 2),
        max 1 (c * Real.sqrt r) ≤ F W ∧ F W ≤ G W ∧ G W ≤ r) ∧
      (∀ r : ℕ, 1 ≤ r →
        F (⊤ : Submodule (ZMod 2) (Fin r → ZMod 2)) ≤ C * Real.sqrt (r * Real.logb 2 (r + 1))) ∧
      (∀ r : ℕ, 1 ≤ r →
        c * Real.sqrt (r * Real.logb 2 (r + 1)) ≤ G (⊤ : Submodule (ZMod 2) (Fin r → ZMod 2)) ∧
        G (⊤ : Submodule (ZMod 2) (Fin r → ZMod 2)) ≤ C * Real.sqrt (r * Real.logb 2 (r + 1))) ∧
      F (⊤ : Submodule (ZMod 2) (Fin 1 → ZMod 2)) = 1 := by sorry

end InteractionElim.Main
