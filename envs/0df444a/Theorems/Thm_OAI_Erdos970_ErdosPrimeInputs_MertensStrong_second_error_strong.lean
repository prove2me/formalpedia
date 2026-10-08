-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosPrimeInputs_MertensStrong_second_error_strong
-- name    : OAI.Erdos970.ErdosPrimeInputs.MertensStrong.second_error_strong
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:27.657754+00:00
-- url     : https://prove2.me/theorems/55ad3c24-29b1-467d-87c6-cc86cfccada7
-- title:
--   Mertens' second theorem with a de la Vallée Poussin error term
-- statement:
--   There are real constants $c>0$, $C>0$ and $a_0>1$ such that for every real $a\ge a_0$,
--
--   $$|E_2(a)|\le C\cdot \mathrm{decay}(c,a),$$
--
--   where $E_2(a)$ (`Erdos970.Mertens.E₂p a`) is $\sum_{p\le a}1/p-\log\log a-M$, the sum over primes $p\le\lfloor a\rfloor$ and $M$ the bundle's constant `Erdos970.Mertens.M` $=\int_2^\infty E_1(t)/(t\log^2t)\,dt+1-\log\log2$ (the Meissel–Mertens constant in integral form, with $E_1$ the error in Mertens' first theorem), and `decay c a` $=\exp(-c\sqrt{\log a})$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.Erdos970.ErdosPrimeInputs.MertensStrong.second_error_strong`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.Erdos970.ErdosPrimeInputs.MertensStrong

open scoped _root_.Erdos970
open Filter
open Asymptotics
open Finset
open scoped Topology
open OAI.Erdos970.ErdosPrimeInputs.PrimeAbel
open OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay

theorem second_error_strong : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < a₀ ∧
    ∀ a : ℝ, a₀ ≤ a → |_root_.Erdos970.Mertens.E₂p a| ≤ C * decay c a := by
  sorry

end OAI.Erdos970.ErdosPrimeInputs.MertensStrong
