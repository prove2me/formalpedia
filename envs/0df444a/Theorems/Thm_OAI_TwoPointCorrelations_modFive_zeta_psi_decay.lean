-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_modFive_zeta_psi_decay
-- name    : OAI.TwoPointCorrelations.modFive_zeta_psi_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:26.905914+00:00
-- url     : https://prove2.me/theorems/4444448f-4019-4253-b796-0931d48a7133
-- title:
--   The prime number theorem with de la Vallée Poussin error, |ψ(x) − x| ≤ C x e^{−c√log x}
-- statement:
--   There are reals $c>0$ and $C>0$ such that for all sufficiently large real $x$,
--
--   $$|\psi(x)-x|\le C\,x\,e^{-c\sqrt{\log x}},$$
--
--   where $\psi$ is Mathlib's Chebyshev function `Chebyshev.psi`, $\psi(x)=\sum_{n\le x}\Lambda(n)$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.modFive_zeta_psi_decay`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter

theorem modFive_zeta_psi_decay : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤
      C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  sorry

end OAI.TwoPointCorrelations
