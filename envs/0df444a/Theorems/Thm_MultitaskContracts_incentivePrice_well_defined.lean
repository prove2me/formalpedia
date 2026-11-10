-- Prove2me | Theorems.Thm_MultitaskContracts_incentivePrice_well_defined
-- name    : MultitaskContracts.incentivePrice_well_defined
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:33:21.618336+00:00
-- url     : https://prove2.me/theorems/300984d6-c770-4c46-81ec-b742bd338a07
-- title:
--   Definition 3 is well defined: $P_S(K)/P_K(K)\le q_k/p_k<1$ for $k\notin S$
-- statement:
--   Let $I$ be an instance of the multitask model in which success on all tasks is the strongest indicator of full effort (eq. (3)). Then for every strategy $S$ and every task $k\notin S$,
--   $$\frac{P_S(K)}{P_K(K)}\ \le\ \frac{q_k}{p_k}\ <\ 1,$$
--   and hence the denominator of the incentive price is positive: $P_K(K)-P_S(K)>0$ for every $S\subsetneq K$.
--
--   This makes $\theta(S)$ a well-defined positive number for every deviation $S$.
--
--   Differences from the source: none.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), §4.1.2, text after Definition 3, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_Instance_StrongestIndicator

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **The incentive price is well defined** (text after Definition 3, §4.1.2, p.13, PDF 15). Under
eqs. (3) and (1): for every strategy `S` and task `k ∉ S`, `P_S(K)/P_K(K) ≤ q_k/p_k < 1`; hence the
denominator `P_K(K) − P_S(K)` of `θ(S)` is positive for every `S ⊊ K`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), §4.1.2, p.13. -/
theorem incentivePrice_well_defined (I : Instance K) (h3 : I.StrongestIndicator) :
    (∀ (S : Finset K) (k : K), k ∉ S →
      I.P S Finset.univ / I.P Finset.univ Finset.univ ≤ I.q k / I.p k ∧ I.q k / I.p k < 1) ∧
    ∀ S : Finset K, S ≠ Finset.univ → 0 < I.P Finset.univ Finset.univ - I.P S Finset.univ := by sorry

end MultitaskContracts
