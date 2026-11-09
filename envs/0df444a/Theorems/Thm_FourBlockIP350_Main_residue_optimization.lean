-- Prove2me | Theorems.Thm_FourBlockIP350_Main_residue_optimization
-- name    : FourBlockIP350.Main.residue_optimization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:12.546648+00:00
-- url     : https://prove2.me/theorems/87edb6d3-35be-4fd7-8306-e1a4d041a2f7
-- title:
--   Lemma 5.1 — Optimization within a residue class
-- statement:
--   Suppose the positive uniform dilation $N$ and $M=kN$ have been computed, and take a canonical residue $q\in\{0,\ldots,M-1\}^k$. A uniform binary algorithm returns a minimizer $v$ of
--   $$\min\{F_q(v):\alpha_q\le v\le\beta_q\},$$
--   its exact integer value and a local vector attaining the inner minimum at $x=q+Mv$, or correctly reports that the residue box is empty. The bound is $f(k,\bar\Delta)(1+|I|+\operatorname{enc}(N))^d$ for one total computable $f$ and absolute $d$.
--
--   Reporting an empty residue box is distinct from infeasibility of the original equations: residual penalties permit positive residuals at the minimizing witness.
--
--   Differences from the source:
--   - encoding: N is the positive uniform period supplied by Proposition 2.6 → N > 0 and UniformDilation (3*k) Δbar N; reason: the same upstream property is exposed as a hypothesis to avoid choosing a noncanonical witness; 3*k is the padded block bound used by Theorem 5.2
--   - encoding: binary time f(k, Δbar)(|I| + log N)^{O(1)} → one fixed finite-alphabet multitape machine; one machine-computable f; one natural exponent; f(k, Δbar)(1+|enc(I)|+|enc(N)|)^d; reason: the supplied period N is part of the binary input; its encoding length is Theta(1+log N), and the canonical residue length is O(k(1+log(kN))) with k absorbed into f
--   - encoding: report infeasibility → report that the residue box is empty; reason: the proof on p. 13 defines this branch by alpha_q,j > beta_q,j; F remains finite even if the original equations are infeasible
--   - encoding: log N in the time bound → self-delimiting binary length enc(N); reason: for positive N the length is Theta(1+log N); the constant overhead is absorbed in the uniform polynomial bound
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 13, Lemma 5.1

import Mathlib
import Definitions.Def_FourBlockIP350_Main_BinaryEncoding
import Definitions.Def_FourBlockIP350_Main_Penalty
import Definitions.Def_FourBlockIP350_Main_Decomposition

namespace FourBlockIP350.Main

open scoped BigOperators

theorem residue_optimization :
    ∃ P : IntMul.MultitapeTM, ∃ f : ℕ → ℕ → ℕ, ComputablePairFunction f ∧
    ∃ d : ℕ, ∀ k n Δ N : ℕ, 0 < k → 0 < n → 0 < Δ → 0 < N →
      UniformDilation (3*k) Δ N →
      ∀ I : FourBlock k n, I.localPart.Bounded Δ → GoodBox I →
      ∀ q : ZVec k, IsResidue (period k N) q →
      ( (¬ ∃ v, ResidueBox I N q v) ∧
          ComputesWithin P (encFourBlock I ++ encNat N ++ encVector (List.finRange k) q)
            [false] (f k Δ * (1 + (encFourBlock I).length + (encNat N).length)^d) ) ∨
      ( ∃ v : ZVec k, ∃ y : LocalCol k n → ℤ, ∃ value : ℤ,
          ResidueBox I N q v ∧
          (∀ w, ResidueBox I N q w → Fq I N q v ≤ Fq I N q w) ∧
          Attains I (q + (period k N : ℤ) • v) y ∧
          F I (q + (period k N : ℤ) • v) = ((value : ℝ) : EReal) ∧
          ComputesWithin P (encFourBlock I ++ encNat N ++ encVector (List.finRange k) q)
            ([true] ++ encVector (List.finRange k) v ++ encInt value ++ encVector (localOrder k n) y)
            (f k Δ * (1 + (encFourBlock I).length + (encNat N).length)^d) ) := by sorry

end FourBlockIP350.Main
