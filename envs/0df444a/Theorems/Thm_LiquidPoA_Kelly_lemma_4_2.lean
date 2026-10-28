-- Prove2me | Theorems.Thm_LiquidPoA_Kelly_lemma_4_2
-- name    : LiquidPoA.Kelly.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:03.992099+00:00
-- url     : https://prove2.me/theorems/05b3e292-7c07-4446-a2cb-0e4eca275de2
-- title:
--   Lemma 4.2, p. 13 — the bound in equation (6) and its equality case
-- statement:
--   Let $M$ be an $n$-player resource allocation mechanism, $n\ge2$, with allocation and payment functions $g^M$ and $p^M$, and let
--
--   $$
--   \lambda^M_1(s)=\Big(\frac{\partial g^M_1(y,s_{-1})}{\partial y}\Big|_{y=s_1}\Big)^{-1}\cdot\frac{\partial p^M_1(y,s_{-1})}{\partial y}\Big|_{y=s_1}.
--   $$
--
--   Then the liquid price of anarchy of $M$ satisfies
--
--   $$
--   LPoA(M)\le\sup_{s\in\mathbb X_n}
--   \frac{\sum_{i\ge2}p_i^M(s)+\lambda_1^M(s)}{\sum_{i\ge2}p_i^M(s)+\lambda_1^M(s)\,g_1^M(s)}.\tag{6}
--   $$
--
--   If, in addition, every $s\in\mathbb X_n$ is an equilibrium of the game $\mathcal G^M(s,1)$, then (6) holds with equality.
--
--   The lemma turns upper and lower bounds on the liquid price of anarchy into the analysis of a single explicit expression in the signal vector, with no reference to valuations or budgets.
--
--   **Formalization Note** $LPoA(M)$ is the supremum over all admissible games and all their equilibria, as on p. 6. The paper's proof restricts to equilibria in $\mathbb X_n$ by the claim of pp. 5–6 that no other signal vector is an equilibrium (up to games whose liquid welfare does not depend on the allocation); that claim uses the continuity of the payment at the zero vector, which is property 8 of the mechanism axioms. User 1 is index $0$; $n\ge2$ makes it exist.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, p. 13, Lemma 4.2 and equation (6)

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- Lemma 4.2, p. 13: the liquid price of anarchy is bounded by the supremum (6), with equality under the equilibrium condition. -/
theorem lemma_4_2 {n : ℕ} (hn : 2 ≤ n) (M : Mechanism n)
    (hM : IsRAMechanism M) :
    (lpoa M ≤ ⨆ (s : Fin n → ℝ) (_ : InX s),
      ratio M s (⟨0, by omega⟩ : Fin n)) ∧
    ((∀ s, InX s →
      IsEquilibrium M (worstGame M s (⟨0, by omega⟩ : Fin n)) s) →
      lpoa M = ⨆ (s : Fin n → ℝ) (_ : InX s),
        ratio M s (⟨0, by omega⟩ : Fin n)) := by sorry

end LiquidPoA.Kelly
