-- Prove2me | Theorems.Thm_LemkeLCP_Existence_lemma_2_p6
-- name    : LemkeLCP.Existence.lemma_2_p6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:04:22.088763+00:00
-- url     : https://prove2.me/theorems/32d01336-aeb6-4fdb-9411-429701abd4d1
-- title:
--   Lemma 2 (p. 6) — Z** has an equilibrium point
-- statement:
--   Let $M$ be a real square matrix of order $n$ and $q\in\mathbb R^n$, and let $Z^*=\{(z,z_0): z\ge0,\ z_0\ge0,\ Mz+z_0e-q\ge0\}$ be the set (9). Let $k$ be a real number such that every extreme point $(z,z_0)$ of $Z^*$ satisfies
--   $$e^{\mathsf T}z<k ,$$
--   and let $Z^{**}=Z(M^{**},q^{**})$ be the bordered set of (12)–(13). If $Z^{**}$ is non-degenerate, then $Z^{**}$ has an equilibrium point: there is $z^*=(z,z_0)\in Z^{**}$ with
--   $$z^{*\mathsf T}w^*=0,\qquad w^*=M^{**}z^*-q^{**}.$$
--
--   The paper proves it by checking that $Z^{**}$ satisfies the hypotheses of Theorem 2 (with $E_0^*$ the only ray of $Z^{**}$ in $Z_0^{**}$). The equilibrium point found is the end of Lemke's augmented path started on $E_0^*$.
--
--   **Formalization Note** "Extreme point of $Z^*$" is the usual convex-geometric notion. The page derives non-degeneracy of $Z^{**}$ from that of $Z^*$ and the choice of $k$, but Def. 3 does not define non-degeneracy for the non-square system $Z^*$; the item therefore assumes non-degeneracy of $Z^{**}$ (Def. 3 applied to the bordered system), which is what the proof's appeal to Theorem 2 uses. The hypothesis on $k$ is kept: without it, $k<0$ makes $Z^{**}$ empty.
-- source:
--   Lemke, Bimatrix equilibrium points and mathematical programming, hal-01885823v1, p. 6, Lemma 2, (12)–(14)

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem lemma_2_p6 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (k : ℝ) (hk : ∀ p ∈ Set.extremePoints ℝ (Zstar M q), ∑ i, p.1 i < k)
    (hnd : NonDegenerate (Mss M) (qss q k)) :
    ∃ p : ι ⊕ Unit → ℝ, IsEquilibriumPoint (Mss M) (qss q k) p := by sorry

end LemkeLCP.Existence
