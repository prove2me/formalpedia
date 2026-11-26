-- Prove2me | Theorems.Thm_JechSetTheory_sch_of_sch_cof_aleph0_same_univ
-- name    : JechSetTheory.sch_of_sch_cof_aleph0_same_univ
-- status  : Proved
-- author  : @teargosling
-- created : 2026-11-26T03:24:24.92913+00:00
-- url     : https://prove2.me/theorems/e4f1e645-0bce-4771-8fd1-462c2761e923
-- title:
--   Jech, Theorem 8.13 (Silver) — SCH at cofinality $\omega$ implies SCH everywhere
-- statement:
--   The Singular Cardinal Hypothesis at a cardinal $\kappa$, written $\mathrm{SCH}(\kappa)$, asserts that if $\kappa$ is singular and $2^{\operatorname{cf}\kappa} < \kappa$, then $\kappa^{\operatorname{cf}\kappa} = \kappa^{+}$ (Jech, Chapter 5, p. 58).
--
--   Suppose $\mathrm{SCH}(\lambda)$ holds for every cardinal $\lambda$ of countable cofinality ($\operatorname{cf}\lambda = \aleph_0$). Then $\mathrm{SCH}(\kappa)$ holds for every cardinal $\kappa$:
--
--   $$\bigl(\forall \lambda,\ \operatorname{cf}\lambda = \aleph_0 \implies \mathrm{SCH}(\lambda)\bigr) \;\Longrightarrow\; \forall \kappa,\ \mathrm{SCH}(\kappa).$$
--
--   This is Silver's second theorem on singular cardinals (Jech, Theorem 8.13), reducing the Singular Cardinal Hypothesis to singular cardinals of countable cofinality. Together with Silver's theorem on GCH (Theorem 8.12), it shows that no failure of SCH can first occur at a singular cardinal of uncountable cofinality.
--
--   **Formalization Note** Both quantifiers range over `Cardinal.{u}` in a single shared universe `u`, and `SCHAt.{u}` from `Definitions.Def_JechStationary` already bundles the hypotheses `k.IsSingular` and `2 ^ k.ord.cof < k` (so the statement holds vacuously for finite and regular cardinals). This fixes the unintended two-universe elaboration (`Cardinal.{u_1}` vs. `Cardinal.{u_2}`) of `JechSetTheory.sch_of_sch_cof_aleph0`.
-- source:
--   Thomas Jech, Set Theory, The Third Millennium Edition, revised and expanded, Springer Monographs in Mathematics, Springer 2003, ISBN 3-540-44085-2, Chapter 8, p. 96, Theorem 8.13 (Silver), with the definition of the Singular Cardinal Hypothesis on p. 58 (Chapter 5)

import Definitions.Def_JechStationary

universe u

open Cardinal Order Set JechSetTheory

namespace JechSetTheory

theorem sch_of_sch_cof_aleph0_same_univ (h : ∀ l : Cardinal.{u}, l.ord.cof = ℵ₀ → SCHAt.{u} l) :
    ∀ k : Cardinal.{u}, SCHAt.{u} k := by sorry

end JechSetTheory
