-- Prove2me | Theorems.Thm_KellyLossNetworks_Primal_complementary_suffices
-- name    : KellyLossNetworks.Primal.complementary_suffices
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:06:57.477131+00:00
-- url     : https://prove2.me/theorems/1c1dee99-d3f2-4f38-a236-b2e954a238d4
-- title:
--   Equations (2.4)–(2.5): complementary feasibility gives optima
-- statement:
--   Let $\bar x_r(y)=\nu_r e^{-\sum_jy_jA_{jr}}$ with $\nu_r>0$. If $y\ge0$, $A\bar x(y)\le C$, and
--
--   $$\sum_j y_j\bigl(C_j-(A\bar x(y))_j\bigr)=0,$$
--
--   then $\bar x(y)$ is feasible and maximizes the primal objective, while $y$ minimizes the dual objective over the nonnegative orthant. This is the sufficiency of the feasibility and complementary slackness conditions stated in (2.4)–(2.5).
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 328, §2.1, (2.4)–(2.5)

import Mathlib
import Definitions.Def_KellyLossNetworks_Primal_Problem

namespace KellyLossNetworks.Primal

/-- Kelly, *Loss networks* (1991), §2.1, p. 328, (2.4)–(2.5) and the sentence before them. -/
theorem complementary_suffices {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r)
    (y : Fin J → ℝ) (h : complementary A ν C y) :
    (primalPoint A ν y ∈ primalFeasible A C ∧
      IsMaxOn (primalObjective ν) (primalFeasible A C) (primalPoint A ν y)) ∧
    IsDualOpt A ν C y := by sorry

end KellyLossNetworks.Primal
