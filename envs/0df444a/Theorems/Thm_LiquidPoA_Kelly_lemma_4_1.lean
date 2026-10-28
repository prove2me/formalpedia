-- Prove2me | Theorems.Thm_LiquidPoA_Kelly_lemma_4_1
-- name    : LiquidPoA.Kelly.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:00.266497+00:00
-- url     : https://prove2.me/theorems/600a7d67-786e-4328-a152-1272ac4dc59f
-- title:
--   Lemma 4.1, p. 10 — an affine worst-case game bounds LPoA
-- statement:
--   Let $M$ be a resource allocation mechanism and $G$ an admissible $n$-player game with $LPoA(G)>1$. Suppose $s\in\mathbb X_n$ is a pure Nash equilibrium with minimum liquid welfare among the equilibria of $G$. There is a player $i^*$ such that
--
--   $$
--   LPoA(G)\le \frac{LW(\widetilde x,G^M(s,i^*))}{LW(g^M(s),G^M(s,i^*))}
--   =\frac{\sum_{i\ne i^*}p_i^M(s)+\lambda_{i^*}^M(s)}{\sum_{i\ne i^*}p_i^M(s)+\lambda_{i^*}^M(s)g_{i^*}^M(s)},
--   $$
--
--   where $\widetilde x$ gives all of the resource to $i^*$. The lemma reduces a game's inefficiency to that of an affine game determined by an equilibrium.
--
--   **Formalization Note** The minimum-welfare condition and $LPoA(G)>1$ are explicit. Ratios use extended nonnegative reals.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, p. 10, Lemma 4.1

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- Lemma 4.1, p. 10: a minimum-welfare equilibrium is bounded by an affine worst-case game. -/
theorem lemma_4_1 {n : ℕ} (M : Mechanism n) (hM : IsRAMechanism M)
    (G : RAGame n) (hG : G.IsAdmissible)
    (hbad : 1 < gameLPoA M G) (s : Fin n → ℝ)
    (heq : IsEquilibrium M G s) (hs : InX s)
    (hmin : ∀ t, IsEquilibrium M G t → LW G (M.alloc s) ≤ LW G (M.alloc t)) :
    ∃ i : Fin n,
      gameLPoA M G ≤
        LW (worstGame M s i) (unitAlloc i) / LW (worstGame M s i) (M.alloc s) ∧
      LW (worstGame M s i) (unitAlloc i) / LW (worstGame M s i) (M.alloc s) =
        ratio M s i := by sorry

end LiquidPoA.Kelly
