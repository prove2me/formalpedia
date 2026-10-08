-- Prove2me | Theorems.Thm_LemkeLCP_Existence_theorem_2
-- name    : LemkeLCP.Existence.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:04:56.808954+00:00
-- url     : https://prove2.me/theorems/acc3be91-2838-49f9-aeea-d1f096a74441
-- title:
--   Theorem 2, p. 4 — if Z is non-degenerate and some Zₛ contains exactly one ray of Z, Z has an odd number of equilibrium points
-- statement:
--   Let $M$ be a real square matrix of order $n$, $q\in\mathbb R^n$, and suppose $Z=\{z\ge0: Mz-q\ge0\}$ is non-degenerate. Suppose that for some index $s$ the set $Z_s=\{z\in Z: z^{\mathsf T}w=z_sw_s\}$ contains precisely one ray of $Z$. Then the set $S$ of equilibrium points of $Z$ is finite and
--   $$|S|\ \text{is odd}.$$
--   In particular $Z$ has an equilibrium point.
--
--   The paper derives this as an immediate corollary of Theorem 1 (a parity argument on the adjacency paths of $Z_s$); it is the form in which existence is applied to the augmented set $Z^{**}$ (Lemma 2, p. 6).
--
--   **Formalization Note** A ray is an open edge of $Z$ with exactly one end-point; "precisely one ray" is unique existence of such an open edge contained in $Z_s$. "An odd number" is expressed as finiteness of $S$ together with oddness of its cardinality.
-- source:
--   Lemke, Bimatrix equilibrium points and mathematical programming, hal-01885823v1, p. 4, Theorem 2

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem theorem_2 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (hnd : NonDegenerate M q)
    (hray : ∃ s : ι, ∃! E : Set (ι → ℝ), IsRay M q E ∧ E ⊆ Zs M q s) :
    (S M q).Finite ∧ Odd (S M q).ncard := by sorry

end LemkeLCP.Existence
