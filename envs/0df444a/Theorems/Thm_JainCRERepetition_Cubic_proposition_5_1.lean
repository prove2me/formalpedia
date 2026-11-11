-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_proposition_5_1
-- name    : JainCRERepetition.Cubic.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:51.209763+00:00
-- url     : https://prove2.me/theorems/95575d6a-f24a-4e6c-9d77-6f64219194db
-- title:
--   Proposition 5.1 — single-copy extraction from smooth preparation
-- statement:
--   There is one universal valid sampler constant $C_{\rm sm}\ge1$. Put $C_{\rm prep}=100C_{\rm sm}$ and $C_{\rm ext}=2^{1/4}\sqrt{C_{\rm prep}}+\sqrt{\ln2}\ge1$. For consistent coordinate targets with finite conditional-comparison divergences and average budgets $m^{-1}\sum_i s_i\le2t$ and $m^{-1}\sum_i\kappa_i\le t$,
--
--   $$\sqrt\varepsilon\le\sqrt{A_C}+\sqrt{C_{\rm prep}}(2t)^{1/4}+\sqrt{(\ln2)t}.$$
--
--   When $0\le t\le1$, the full simplified conclusion is $\sqrt\varepsilon\le\sqrt{A_C}+C_{\rm ext}t^{1/4}$. The targets' fixed answer readers reproduce the actual conditional repeated-strategy marginal. Thus each positive-slack preparation supplies a legal strategy under fresh questions, without requiring the preparation infimum or game supremum to be attained.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
--   - generalization: coordinate views of the postselection vector with consistent designated answers → any copied-input target families with the same conditional question/answer readout laws and comparison budgets; reason: the extraction argument uses only these laws, local finite preparation and the two budgets; the constructed full coordinate views satisfy them
--   - encoding: Cprep and Cext from the universal smooth sampler → one universal Csm witness with the exact expressions Cprep=100 Csm and Cext=2^(1/4) sqrt(Cprep)+sqrt(ln 2); reason: all constant witnesses precede every game, dimension, strategy, checked set and coordinate family
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 31, Proposition 5.1, Eqs. (47)–(48); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_extraction

open scoped BigOperators
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic

theorem proposition_5_1 :
    ∃ Csm : ℝ, 1 ≤ Csm ∧ SamplingConstant Csm ∧
      let Cprep := 100*Csm
      let Cext := Real.rpow 2 (1/4 : ℝ) * Real.sqrt Cprep + Real.sqrt (Real.log 2)
      1 ≤ Cext ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
        [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
        (G : QuantumParallelRepetition.Game X Y A B) (n : ℕ)
        (S : QuantumParallelRepetition.Strategy (G.repeat n))
        (C : Finset (Fin n)) (F : Fin n → TargetBranch X Y A B),
        C ≠ Finset.univ → 0 < checkedProbability S C →
        branchesConsistent S C F → branchesValid C F →
        (∑ i ∈ unchecked C, branchS (F i)) / (unchecked C).card ≤ 2 * budgetRatio S C →
        (∑ i ∈ unchecked C, classicald (F i).family.posterior.p (priorLaw G).p) /
          (unchecked C).card ≤ budgetRatio S C →
        let ε := 1 - QuantumParallelRepetition.entangledValue G
        Real.sqrt ε ≤ Real.sqrt (meanRejection S C) +
          Real.sqrt Cprep * Real.rpow (2 * budgetRatio S C) (1/4 : ℝ) +
          Real.sqrt (Real.log 2 * budgetRatio S C) ∧
        (0 ≤ budgetRatio S C → budgetRatio S C ≤ 1 →
          Real.sqrt ε ≤ Real.sqrt (meanRejection S C) +
            Cext * Real.rpow (budgetRatio S C) (1/4 : ℝ)) := by sorry

end JainCRERepetition.Cubic
