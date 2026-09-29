-- Prove2me | Theorems.Thm_JechSetTheory_sch_of_sch_cof_aleph0
-- name    : JechSetTheory.sch_of_sch_cof_aleph0
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T02:33:54.403952+00:00
-- url     : https://prove2.me/theorems/447a51ff-811d-49c9-ba61-1ff299b281f9
-- title:
--   Jech, Theorem 8.13 (Silver) — SCH at cofinality $\omega$ implies SCH everywhere
-- statement:
--   The **Singular Cardinal Hypothesis** (SCH) is the statement: for every singular cardinal $\kappa$, if $2^{\operatorname{cf}\kappa} < \kappa$ then $\kappa^{\operatorname{cf}\kappa} = \kappa^{+}$ (Jech, p. 58). Write $\mathrm{SCH}(\kappa)$ for the instance of this statement at a single cardinal $\kappa$.
--
--   **Theorem (Silver; Jech 8.13).** If $\mathrm{SCH}(\lambda)$ holds for every cardinal $\lambda$ of cofinality $\omega$, then $\mathrm{SCH}(\kappa)$ holds for every cardinal $\kappa$.
--
--   Together with Theorem 8.12 this is what makes the singular cardinal problem a question about cofinality $\omega$: no failure of SCH can first appear at a singular cardinal of uncountable cofinality. Magidor's consistency results and Shelah's pcf theory both live on the cofinality-$\omega$ side of this dichotomy.
--
--   **Formalization Note** $\mathrm{SCH}(\kappa)$ is the predicate `SCHAt` of the definition bundle: it already contains the singularity hypothesis and the assumption $2^{\operatorname{cf}\kappa} < \kappa$, so at regular $\kappa$ it holds vacuously and the conclusion "for all $\kappa$" carries no extra content there. Cofinality $\omega$ is written as $\operatorname{cf}(\kappa.\mathrm{ord}) = \aleph_0$.
-- source:
--   Thomas Jech, Set Theory, The Third Millennium Edition, revised and expanded, Springer Monographs in Mathematics, Springer 2003, ISBN 3-540-44085-2, Chapter 8, p. 96, Theorem 8.13 (Silver), with the definition of the Singular Cardinal Hypothesis on p. 58 (Chapter 5)

import Mathlib
import Definitions.Def_JechStationary

open Cardinal Order Set JechSetTheory

namespace JechSetTheory

theorem sch_of_sch_cof_aleph0 (h : ∀ l : Cardinal, l.ord.cof = ℵ₀ → SCHAt l) :
    ∀ k : Cardinal, SCHAt k := by sorry

end JechSetTheory
