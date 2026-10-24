-- Prove2me | Theorems.Thm_OAI_BassTrace_bassTrace
-- name    : OAI.BassTrace.bassTrace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:11:21.595654+00:00
-- url     : https://prove2.me/theorems/a4830113-6a4e-4652-a40e-5e36b5fbed30
-- title:
--   Bass trace conjecture for idempotent matrices over ℂ[G]: the trace vanishes at infinite-order conjugacy classes (OpenAI Bass trace)
-- statement:
--   **Notation** (definitions bundle `OAIQWBAS001` of this split). For a group $G$, an element $a = \sum_h a_h h$ of the complex group algebra $\mathbb C[G]$ (`MonoidAlgebra ℂ G`) and $g \in G$, the class coefficient `classCoefficient g a` is $\sum_{h \sim g} a_h$, the sum of the coefficients of $a$ over the elements conjugate to $g$. For a $q \times q$ matrix $e$ over $\mathbb C[G]$, `idempotentTraceCoefficient e g` is the class coefficient at $g$ of the matrix trace $\sum_i e_{ii}$. When $e$ is idempotent this is the coefficient at the conjugacy class of $g$ of the Hattori–Stallings trace of the projective module $e\,\mathbb C[G]^q$.
--
--   **The statement.** Let $G$ be any group, $q$ a natural number, and $e$ a $q \times q$ matrix over $\mathbb C[G]$ with $e e = e$. For every $g \in G$ of infinite order,
--   $$\sum_{h \sim g}\Bigl(\sum_{i=1}^{q} e_{ii}\Bigr)_h \;=\; 0 .$$
--
--   This is the matrix form of the paper's Theorem 1.1. The published goal `OAI.BassTrace.RightProjective.bassTraceModules_vanishing_and_support` follows from it by additivity over $K_0(\mathbb C[G])$.
--
--   Lean: `OAI.BassTrace.bassTrace`, OpenAI's theorem of that name (in `lean/OAI/RingTheory/BassTrace/MatrixVanishing.lean`).
-- source:
--   OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 207; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/BassTrace/MatrixVanishing.lean (declaration OAI.BassTrace.bassTrace)

import Mathlib
import Definitions.Def_OAIQWBAS001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace

open scoped Classical BigOperators

theorem bassTrace {G : Type*} [Group G] {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G))
    (he : e*e=e) (g : G) (hg : ¬IsOfFinOrder g) :
    idempotentTraceCoefficient e g=0 := by
  sorry

end BassTrace

end

end OAI
end
