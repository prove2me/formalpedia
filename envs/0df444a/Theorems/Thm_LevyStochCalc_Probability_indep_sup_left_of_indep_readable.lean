-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_indep_sup_left_of_indep_readable
-- name    : LevyStochCalc.Probability.indep_sup_left_of_indep_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:37.515985+00:00
-- url     : https://prove2.me/theorems/c2c528da-fe2a-4d38-a81e-84fdbfe1a3dc
-- title:
--   Independence After Joining the Left Sigma-Algebras
-- statement:
--   This is a sigma-algebra join lemma for independence.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space and let $m_1,m_2,m_3\subseteq\mathcal F$ be measurable spaces. Assume:
--
--   1. $m_1\perp m_3$ under $P$.
--   2. $m_2\perp(m_1\vee m_3)$ under $P$.
--
--   Then the join of the first two sigma-algebras is independent of the third:
--
--   $$m_1\vee m_2\perp m_3.$$
--
--   This technical result packages the product-measure calculation needed to iterate independence along an ordered family of sigma-algebras.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem indep_sup_left_of_indep (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) (h₃ : m₃ ≤ mΩ)
--       (h13 : Indep m₁ m₃ P) (h2 : Indep m₂ (m₁ ⊔ m₃) P) : Indep (m₁ ⊔ m₂) m₃ P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/IndepJoin`](https://prove2.me/theorems/15fc6375-12e2-4c9f-a8c1-138171ac0589).
--
--   Next: [`indep_iSup_of_finset`](https://prove2.me/theorems/203c9447-e491-43d7-8d96-6b87e13fa487).
--
--   [Source excerpt, lines 48–49](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/IndepJoin.lean#L48-L49) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/IndepJoin.lean#L47-L62 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.IndepJoin`, declaration `LevyStochCalc.Probability.indep_sup_left_of_indep`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_IndepJoin

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/IndepJoin.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} {m₁ m₂ m₃ mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

theorem LevyStochCalc.Probability.indep_sup_left_of_indep_readable (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) (h₃ : m₃ ≤ mΩ)
    (h13 : Indep m₁ m₃ P) (h2 : Indep m₂ (m₁ ⊔ m₃) P) : Indep (m₁ ⊔ m₂) m₃ P := by sorry
