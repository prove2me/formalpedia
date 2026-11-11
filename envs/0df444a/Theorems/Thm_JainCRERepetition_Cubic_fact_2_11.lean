-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_fact_2_11
-- name    : JainCRERepetition.Cubic.fact_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:27.707109+00:00
-- url     : https://prove2.me/theorems/45a01004-2360-48b4-874e-a70de372c5f6
-- title:
--   Fact 2.11 — isometric dilation and coherent strategy representations
-- statement:
--   Every finite-dimensional quantum channel $\mathcal N:I\to O$ has a finite environment and an isometry $V$ such that
--
--   $$V^\dagger V=1,\qquad \mathcal N(\rho)=\operatorname{Tr}_E(V\rho V^\dagger).$$
--
--   In particular every finite-dimensional repeated-game strategy admits the coherent resource and local isometry representation used in Definition 3.2. This application retains all measured answers and implementation environments, so the operational construction does not assume the existence of an optimal entangled strategy.
--
--   Differences from the source:
--   - encoding: channel dilation and the purification/dilation application of Definition 3.2 → one conjunction giving the isometry and a coherent representation of every actual repeated strategy; reason: the second clause exposes the source construction needed by the coordinate definitions
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 14, Fact 2.11; pp. 22–23, Definition 3.2; pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_repeated

open scoped BigOperators
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic

theorem fact_2_11 :
    (∀ (I O : Type) [Fintype I] [Fintype O] [DecidableEq I]
      (N : WildeQIT.QChannel I O),
      ∃ (k : ℕ) (V : Matrix (O × Fin k) I ℂ), Vᴴ * V = 1 ∧
        ∀ ρ : Op I, trR (V * ρ * Vᴴ) = N.apply ρ) ∧
    (∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
      [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
      [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
      (G : QuantumParallelRepetition.Game X Y A B) (n : ℕ)
      (S : QuantumParallelRepetition.Strategy (G.repeat n)), Nonempty (CoherentStrategy S)) := by sorry

end JainCRERepetition.Cubic
