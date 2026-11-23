-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_11_sperner_existence
-- name    : ManipPotential.proposition_6_11_sperner_existence
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:23:33.723929+00:00
-- url     : https://prove2.me/theorems/6b930650-9cf3-4c95-a834-cc6c52d854ea
-- title:
--   Proposition 6.11 — lower bound (15) and Sperner/compactness existence
-- statement:
--   There is an integer threshold $T>m$ such that, for every external-coordinate vector $y$ with
--   $$1<y_s<1+\frac1{32}\qquad(s\in\mathcal L(C)\setminus L)$$
--   and every $\tau\in(T,T+1)$, the parameter box contains a common junction, and every common junction with parameters $(y,\tau)$ satisfies the uniform positivity estimate (15), in particular $P_r>1$ for every ranking $r$. The existence assertion is obtained by combining Sperner fully labelled simplices of successively finer triangulations with compactness; the positivity assertion is obtained from Corollary 6.7 at $P^\nu=P$ and equation (15).
-- source:
--   Berker–Conitzer–Hartman–Liu–Oesterheld, How Many Votes Is a Lie Worth?, arXiv:2602.22838 (v3, 2026-11-03), Proposition 6.11, pp.33–34, especially equation (15) and the final compactness paragraph on p.34.

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_cycTotal

namespace ManipPotential

/-- Proposition 6.11, the lower bound (15) and the Sperner/compactness existence argument, pp.33--34. -/
theorem proposition_6_11_sperner_existence {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g) :
    ∃ T : ℝ, (m : ℝ) < T ∧
      ∀ (y : ExtRanking m → ℝ) (τ : ℝ),
        (∀ s, 1 < y s ∧ y s < 1 + 1 / 32) → T < τ → τ < T + 1 →
        (∀ P : Ranking m → ℝ, IsCommonJunction g P →
          (∀ s : ExtRanking m, P s.1 = y s) → cycTotal P = τ → ∀ r, 1 < P r) ∧
        ∃ P : Ranking m → ℝ, IsCommonJunction g P ∧
          (∀ s : ExtRanking m, P s.1 = y s) ∧ cycTotal P = τ ∧ ∀ r, 1 < P r := by sorry
