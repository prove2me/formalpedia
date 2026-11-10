-- Prove2me | Theorems.Thm_MultitaskContracts_corollary_10
-- name    : MultitaskContracts.corollary_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:32:46.120061+00:00
-- url     : https://prove2.me/theorems/6c5bb6e9-8693-455d-8ee7-6034496f1848
-- title:
--   Corollary 10 — in every instance, full effort $K$ is implementable
-- statement:
--   In every instance of the multitask model (any dependence between tasks), full effort is implementable: there is a contract $t:2^K\to\mathbb R_{\ge0}$ such that for every strategy $S\subseteq K$,
--   $$\mathbb E_{Y\sim P_K}[t(Y)]-c(K)\ \ge\ \mathbb E_{Y\sim P_S}[t(Y)]-c(S).$$
--
--   Consequently the Min-Pay optima over bundle contracts are finite, and an optimal contract exists.
--
--   Differences from the source: none.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Corollary 10, App. C, p.55 (PDF p.57)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Corollary 10** (App. C, p.55, PDF 57). In every instance, `K` is implementable: some
contract `t : 2^K → ℝ_{≥0}` implements full effort.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Corollary 10, p.55.

**Formalization Note.** "Implementable" is the existence of a bundle (nonnegative) contract `t`
with `K ∈ S*_t`. -/
theorem corollary_10 (I : Instance K) :
    ∃ t ∈ bundle K, I.Implements t Finset.univ := by sorry

end MultitaskContracts
