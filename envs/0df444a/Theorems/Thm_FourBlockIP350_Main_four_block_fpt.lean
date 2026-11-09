-- Prove2me | Theorems.Thm_FourBlockIP350_Main_four_block_fpt
-- name    : FourBlockIP350.Main.four_block_fpt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:00.719148+00:00
-- url     : https://prove2.me/theorems/a8937f15-8054-41d6-bf6b-6c9234184036
-- title:
--   Theorem 1.1 — Fixed-parameter algorithm for general 4-block ILP
-- statement:
--   There exist a single uniform executable algorithm $P$, a total computable function $f:\mathbb N^2\to\mathbb N$, and an absolute exponent $d$, such that every nonuniform 4-block integer program $I$ is solved within
--   $$f(k,\bar\Delta)(1+|\operatorname{enc}(I)|)^d$$
--   binary steps. Here $k\ge1$ is the block dimension, and $\bar\Delta\ge1$ bounds only the local-column blocks $B^{(i)},D^{(i)}$. The number of bricks, entries of the global-column blocks $A^{(0)},C^{(i)}$, costs, right-hand sides and bound magnitudes are arbitrary input data. Lower endpoints may be $-\infty$ and upper endpoints $+\infty$; blocks need not be uniform.
--
--   The output is one of an optimal integer vector and its exact value, infeasibility iff there is no integer feasible vector, or unboundedness below, including integer feasibility and arbitrarily low integer cost. Correctness and the charged execution bound are conclusions for every instance. The same $P,f,d$ work for all dimensions, brick counts and coefficients.
--
--   This is the full headline result, including infinite original bounds and all three solver outcomes.
--
--   Differences from the source:
--   - encoding: binary time f(k, Δbar) |I|^{O(1)} → one fixed finite-alphabet multitape machine; one machine-computable f; one natural exponent; f(k, Δbar)(1+|enc(I)|)^d; reason: the machine steps and delimited dense encoding make the source computational convention explicit; dense and block-list lengths are polynomially related
--   - encoding: returns an optimal integer solution → also returns its exact integer objective value; reason: the value is determined by the returned vector and input costs and is computable in polynomial binary time
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 3, Theorem 1.1

import Mathlib
import Definitions.Def_FourBlockIP350_Main_BinaryEncoding

namespace FourBlockIP350.Main

open scoped BigOperators

theorem four_block_fpt :
    ∃ P : IntMul.MultitapeTM, ∃ f : ℕ → ℕ → ℕ, ComputablePairFunction f ∧
    ∃ d : ℕ, ∀ k n Δ : ℕ, 0 < k → 0 < n → 0 < Δ →
      ∀ I : FourBlock k n, I.localPart.Bounded Δ →
      ∃ a : Answer (BlockCol k n), CorrectAnswer I.program a ∧
        ComputesWithin P (encFourBlock I) (encAnswer (blockOrder k n) a)
          (f k Δ * (1 + (encFourBlock I).length)^d) := by sorry

end FourBlockIP350.Main
