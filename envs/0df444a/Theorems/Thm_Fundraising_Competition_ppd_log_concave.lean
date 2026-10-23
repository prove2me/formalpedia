-- Prove2me | Theorems.Thm_Fundraising_Competition_ppd_log_concave
-- name    : Fundraising.Competition.ppd_log_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:10.477029+00:00
-- url     : https://prove2.me/theorems/4b6aa8ee-2074-4549-bfd7-8d4fee92a348
-- title:
--   Proof of Proposition 1, p. S12 — under Assumption 1, δ_i(s_i)Σ_a w^a_i θ^{J_a}_i(s) is log-concave in s_i on [a_i, b_i]
-- statement:
--   Under the standing hypotheses and Assumption 1, for every HO $i$ and every profile $(s;x)$ with every effort $x_j \in [0,1]$, the function
--   $$t \mapsto \log PPD_i\big((s_{-i}, t); x\big) = \log\Big(\delta_i(t)\, z \sum_{a\in A_i} w^a_i\, \theta^{J_a}_i(s_{-i}, t)\Big)$$
--   is concave on $[a_i, b_i]$.
--
--   Log-concavity of each HO's objective in its own base utility is what makes the first-order (KKT) conditions (7) characterize best responses, and gives convex best-response sets for the existence argument.
--
--   **Formalization Note.** The positive constant $z$ is included (it does not affect concavity of the logarithm). Assumption 1 is used as printed ("$\le$"), which yields concavity, not strict concavity; the paper's proof writes "$<$". The paper writes $\delta(s)$ for $\delta_i(s_i)$.
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), p. S12 (PDF 45), proof of Proposition 1, sentence after (S8)

import Mathlib
import Definitions.Def_Fundraising_Competition_Setting

namespace Fundraising.Competition

theorem ppd_log_concave {n : ℕ} (S : Setting n) (hS : Standing S) (hA : Assumption1 S)
    (s x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    ConcaveOn ℝ (Set.Icc (S.a i) (S.b i))
      (fun t => Real.log (PPD S (Function.update s i t) x i)) := by sorry

end Fundraising.Competition
