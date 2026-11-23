-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_clsHard_trans
-- name    : NetworkEquilibriumCLS.LinearNash.clsHard_trans
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:42:51.876258+00:00
-- url     : https://prove2.me/theorems/62d4affd-84b7-48bd-a44a-17f62e9d712e
-- title:
--   CLS-hardness is preserved along a forward search reduction
-- statement:
--   If $Q$ is CLS-hard and $Q$ admits a polynomial-time search reduction to $R$, then $R$ is CLS-hard:
--   \[
--   \operatorname{CLSHard}(Q)\quad\text{and}\quad Q\le_p R
--   \qquad\Longrightarrow\qquad \operatorname{CLSHard}(R).
--   \]
--
--   Indeed, every $S\in\mathrm{CLS}$ first reduces to $Q$ by hardness, and the two reductions compose. This is the standard transitivity step used when replacing the reference problem 3D-Continuous-Localopt by a chain of intermediate problems.
--
--   **Formalization Note** The search problems use the public `NetworkEquilibriumCLS.LinearNash` representation and the reduction is the all-answers polynomial-time Levin reduction `CardinalMatching.SearchReduces`. Composition is the separately proved `ConstrSOSP.searchReduces_trans`.
-- source:
--   Daskalakis–Papadimitriou, SODA 2011, §2.1, p.794, definition of CLS via polynomial-time search reductions; public definitions `NetworkEquilibriumCLS.LinearNash.CLSHard` and `CardinalMatching.SearchReduces`; reduction transitivity as recorded in Kontogiannis–Panageas–Pollatos, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Theorems.Thm_ConstrSOSP_searchReduces_trans

open NetworkEquilibriumCLS.LinearNash

theorem NetworkEquilibriumCLS.LinearNash.clsHard_trans {Q R : SearchProblem}
    (hQ : CLSHard Q) (hQR : SearchReduces Q R) : CLSHard R := by sorry
