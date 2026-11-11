-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_corollary_5_2
-- name    : JainCRERepetition.Cubic.corollary_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:41.74629+00:00
-- url     : https://prove2.me/theorems/2371538f-fd91-42ec-8afd-ec943292153e
-- title:
--   Corollary 5.2 — conditional rejection from the information budget
-- statement:
--   For every finite game with gap $\varepsilon=1-\omega^*(G)>0$, every actual repeated strategy and every supported proper checked set, let $t=B_C/m$ and $A_C$ be the mean unchecked rejection. With one universal $C_{\rm ext}=2^{1/4}\sqrt{100C_{\rm sm}}+\sqrt{\ln2}\ge1$,
--
--   $$t\le\frac{\varepsilon^2}{16C_{\rm ext}^4}\Longrightarrow A_C\ge\frac\varepsilon4.$$
--
--   The second conclusion is retained in full: for every $0<\delta\le\varepsilon$,
--
--   $$t\le\frac{\delta^4}{8^4C_{\rm ext}^4\varepsilon^2}\Longrightarrow A_C\ge\varepsilon-\frac\delta4.$$
--
--   Both thresholds use the constants of Proposition 5.1. The second clause remains part of this source milestone even though the mission goal is the all-win theorem.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
--   - encoding: the universal Cext from Proposition 5.1 → one universal sampler witness Csm with Cext=2^(1/4) sqrt(100 Csm)+sqrt(ln 2); reason: the witness precedes every game, strategy and checked set and preserves the exact source constant
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 33, Corollary 5.2, Eqs. (49)–(50); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_repeated

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem corollary_5_2 :
    ∃ Csm : ℝ, 1 ≤ Csm ∧ SamplingConstant Csm ∧
      let Cext := Real.rpow 2 (1/4 : ℝ) * Real.sqrt (100*Csm) + Real.sqrt (Real.log 2)
      1 ≤ Cext ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
        [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
        (G : QuantumParallelRepetition.Game X Y A B) (n : ℕ)
        (S : QuantumParallelRepetition.Strategy (G.repeat n))
        (C : Finset (Fin n)), C ≠ Finset.univ → 0 < checkedProbability S C →
        let ε := 1 - QuantumParallelRepetition.entangledValue G
        0 < ε →
        (budgetRatio S C ≤ ε^2/(16*Cext^4) → ε/4 ≤ meanRejection S C) ∧
        (∀ δ : ℝ, 0 < δ → δ ≤ ε →
          budgetRatio S C ≤ δ^4/(8^4*Cext^4*ε^2) → ε-δ/4 ≤ meanRejection S C) := by sorry
end JainCRERepetition.Cubic
