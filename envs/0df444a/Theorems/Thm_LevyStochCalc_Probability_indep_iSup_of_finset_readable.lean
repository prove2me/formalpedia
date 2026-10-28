-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_indep_iSup_of_finset_readable
-- name    : LevyStochCalc.Probability.indep_iSup_of_finset_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:32.565582+00:00
-- url     : https://prove2.me/theorems/203c9447-e491-43d7-8d96-6b87e13fa487
-- title:
--   Independence Of A Countable Sigma-Algebra Supremum
-- statement:
--   Let $(\Omega,P)$ be a probability space, let $m_i$ be a family of sigma-algebras indexed by $\iota$, and let $m'$ be another sigma-algebra. Assume $m_i\leq m_\Omega$ for every $i$ and $m'\leq m_\Omega$. If for every finite set $S\subseteq\iota$,
--
--   $$\bigvee_{i\in S}m_i\ \text{ is independent of }m',$$
--
--   then
--
--   $$\bigvee_{i\in\iota}m_i\ \text{ is independent of }m'.$$
--
--   This is a general independence-extension lemma from finite subjoins to the full supremum.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem indep_iSup_of_finset {ι : Type*} {m : ι → MeasurableSpace Ω} {m' : MeasurableSpace Ω}
--       (h_le : ∀ i, m i ≤ mΩ) (h_le' : m' ≤ mΩ)
--       (h : ∀ S : Finset ι, Indep (⨆ i ∈ S, m i) m' P) :
--       Indep (⨆ i, m i) m' P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/IndepJoin`](https://prove2.me/theorems/15fc6375-12e2-4c9f-a8c1-138171ac0589).
--
--   Previous: [`indep_sup_left_of_indep`](https://prove2.me/theorems/c2c528da-fe2a-4d38-a81e-84fdbfe1a3dc).
--
--   [Source excerpt, lines 88–91](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/IndepJoin.lean#L88-L91) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/IndepJoin.lean#L87-L102 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.IndepJoin`, declaration `LevyStochCalc.Probability.indep_iSup_of_finset`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_IndepJoin

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/IndepJoin.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} {m₁ m₂ m₃ mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

theorem LevyStochCalc.Probability.indep_iSup_of_finset_readable {ι : Type*} {m : ι → MeasurableSpace Ω} {m' : MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ mΩ) (h_le' : m' ≤ mΩ)
    (h : ∀ S : Finset ι, Indep (⨆ i ∈ S, m i) m' P) :
    Indep (⨆ i, m i) m' P := by sorry
