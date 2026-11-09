-- Prove2me | Theorems.Thm_FourBlockIP350_Main_finite_bounds_solver
-- name    : FourBlockIP350.Main.finite_bounds_solver
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:59.462334+00:00
-- url     : https://prove2.me/theorems/14dc227b-abb9-45e8-b4bc-9a51696b56ea
-- title:
--   Theorem 5.2 — Solving instances with finite bounds
-- statement:
--   There exist one binary algorithm, one total computable function $f$ and one absolute exponent $d$ that solve every nonuniform 4-block integer program $I$ with finite integral bounds in
--   $$f(k,\bar\Delta)(1+|\operatorname{enc}(I)|)^d$$
--   steps. The output is an optimal integer vector, with its exact objective value, or an infeasibility report. There is no consistency or feasibility assumption on the input intervals or equations. Only local-column blocks have their entries bounded by $\bar\Delta$.
--
--   This provides the finite-bounds solver used in removing infinite bounds.
--
--   Differences from the source:
--   - encoding: binary time f(k, Δbar) |I|^{O(1)} → one fixed finite-alphabet multitape machine; one machine-computable f; one natural exponent; f(k, Δbar)(1+|enc(I)|)^d; reason: the machine steps and delimited dense encoding make the source computational convention explicit; dense and block-list lengths are polynomially related
--   - encoding: returns an optimal solution or infeasibility → also returns the exact integer cost of an optimal solution; reason: this value is already available in the residue solver; evaluating an integral linear objective has polynomial bit cost and changes no instance
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 15, Theorem 5.2

import Mathlib
import Definitions.Def_FourBlockIP350_Main_BinaryEncoding

namespace FourBlockIP350.Main

open scoped BigOperators

theorem finite_bounds_solver :
    ∃ P : IntMul.MultitapeTM, ∃ f : ℕ → ℕ → ℕ, ComputablePairFunction f ∧
    ∃ d : ℕ, ∀ k n Δ : ℕ, 0 < k → 0 < n → 0 < Δ →
      ∀ I : FourBlock k n, I.localPart.Bounded Δ → FiniteBounds I →
      ∃ a : Answer (BlockCol k n), CorrectAnswer I.program a ∧
        a ≠ Answer.unbounded ∧
        ComputesWithin P (encFourBlock I) (encAnswer (blockOrder k n) a)
          (f k Δ * (1 + (encFourBlock I).length)^d) := by sorry

end FourBlockIP350.Main
