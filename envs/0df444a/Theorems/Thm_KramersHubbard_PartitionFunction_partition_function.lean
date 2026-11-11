-- Prove2me | Theorems.Thm_KramersHubbard_PartitionFunction_partition_function
-- name    : KramersHubbard.PartitionFunction.partition_function
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:04.083718+00:00
-- url     : https://prove2.me/theorems/864cae17-309f-42b2-be2e-092a43f913f3
-- title:
--   Theorem 2 — Polynomial-time partition function estimation
-- statement:
--   For every attractive Kramers Hamiltonian $H=H_0-\sum_iU_i n(v_i)n(\Theta v_i)$ on the full Fock space of $2N$ modes, every $\beta>0$ and every $\varepsilon>0$, there is one uniform classical randomized algorithm with
--
--   $$\Pr\big[(1-\varepsilon)Z\le\widehat Z\le(1+\varepsilon)Z\big]\ge\frac34,\qquad Z=\operatorname{Tr}e^{-\beta H}>0,$$
--
--   and runtime polynomial in $N,r,\beta,\Lambda,\varepsilon^{-1}$, where $\Lambda=\|h\|_1+\sum_iU_i$. More precisely, one finite program and constants $C>0$, $d\in\mathbb N$ work for every input and halt on every uniform-draw tape by $\lceil C(1+N+r+\beta+\Lambda+\varepsilon^{-1})^d\rceil$ charged scalar steps. Its output is the value it actually computes. The success event is measurable under independent uniform draws.
--
--   There are no locality, interaction-strength, rationality, high-temperature or assumed-sampling hypotheses. The cases $r=0$, all $U_i=0$, and $N=0$ whenever admissible remain in scope. This is the full partition-function algorithmic target, not an identity for a Trotterized surrogate.
--
--   Differences from the source:
--   - encoding: complex Fock operators and one-based mode labels → occupation-basis matrices and zero-based Fin labels, with complex equalities to explicit real witnesses where needed; reason: the occupation basis is the entire Fock space, including the vacuum, and preserves the ordered CAR conventions
--   - reading: arbitrary complex and real input with an unspecified classical operation-count computation model → one finite exact-arithmetic pointer program with rational code constants, scalar exp and sqrt, comparisons and independent uniform draws, each charged one step; reason: the source gives no bit encoding; scalar operations express its ideal arithmetic/exponential reading, while every matrix evaluation, transition, independent restart and estimate must be implemented by the program
--   - reading: Theorem 2 says time polynomial; Section 4.4 describes an expected constant number of restarts → one uniform polynomial worst-case bound on all valid random tapes; reason: bounded restarts and finite runs are included in the success guarantee; this makes the unqualified theorem runtime precise without assuming an efficient sampler
--   - reading: Lambda uses the notation norm h subscript 1 without a computational norm convention → the Schatten trace norm, the sum of absolute Hermitian eigenvalues; reason: this is the prescribed trace-norm reading; standard matrix 1-norm alternatives differ by polynomial factors in the separately present mode count
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Theorem 2, p.4; Section 4.4, pp.17-18; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Machine

noncomputable section
open scoped BigOperators ENNReal
open Matrix MeasureTheory

namespace KramersHubbard.PartitionFunction

/-- Theorem 2, p.4. One finite program and one polynomial majorant work for
    every instance. The bound is worst-case, including draws and capped restarts. -/
theorem partition_function :
    ∃ (P : Program) (C : ℝ) (d : ℕ), AdmissibleProgram P ∧ 0 < C ∧
      ∀ (N r : ℕ) (D : Data N r), Attractive D →
      ∀ (β eps : ℝ), 0 < β → 0 < eps →
        (∀ omega : ℕ → ℝ, (∀ j, omega j ∈ Set.Icc (0 : ℝ) 1) →
          (machineRun P (initialState D β eps) omega (timeBound D β eps C d)).halted = true ∧
          (machineRun P (initialState D β eps) omega (timeBound D β eps C d)).work ≤
            timeBound D β eps C d) ∧
        ∃ Z : ℝ, 0 < Z ∧ partition D β = (Z : ℂ) ∧
          MeasurableSet (successEvent P D β eps C d Z) ∧
          (3/4 : ℝ≥0∞) ≤ uniformTape (successEvent P D β eps C d Z) := by sorry

end KramersHubbard.PartitionFunction
