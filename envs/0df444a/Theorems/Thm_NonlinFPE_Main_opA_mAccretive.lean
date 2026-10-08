-- Prove2me | Theorems.Thm_NonlinFPE_Main_opA_mAccretive
-- name    : NonlinFPE.Main.opA_mAccretive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:39.381588+00:00
-- url     : https://prove2.me/theorems/cf46c2a5-9c19-4186-b497-47eff3cd4b30
-- title:
--   §3.1, pp. 9 and 19 — under (H1)–(H3), the operator A of (3.8)–(3.9) is m-accretive in L¹
-- statement:
--   Assume (H1)–(H3). Then the operator
--   $$Au = -\sum_{i,j=1}^d D^2_{ij}\big(a_{ij}(x,u)u\big) + \operatorname{div}\big(b(x,u)u\big), \qquad D(A) = \{u \in L^1 : Au \in L^1\},$$
--   of (3.8)–(3.9) is m-accretive in $L^1(\mathbb R^d)$: $R(I+\lambda A) = L^1$ and (3.3) holds for all $\lambda > 0$.
--
--   It is the hypothesis of the Crandall–Liggett theorem in the proof of Theorem 3.4.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, §3.1, p. 9 ("we must prove that A is m-accretive") and proof of Theorem 3.4, p. 19

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- §3.1, pp. 9 and 19, under (H1)–(H3): the operator `A` of (3.8)–(3.9) is m-accretive in `L¹`. -/
theorem opA_mAccretive {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ) (γ : ℝ) (hND : HypND a b γ) :
    IsMAccretive (opA a b) := by sorry

end NonlinFPE.Main
