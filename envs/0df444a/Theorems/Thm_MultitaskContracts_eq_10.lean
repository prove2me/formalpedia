-- Prove2me | Theorems.Thm_MultitaskContracts_eq_10
-- name    : MultitaskContracts.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:34:36.689074+00:00
-- url     : https://prove2.me/theorems/d6b2c0a6-7a63-404a-b050-dd9bdf344f0a
-- title:
--   Eq. (10) — an AoN contract implements $K$ iff $t(K)\ge\theta(S)$ for all $S\subsetneq K$; $\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}=P_K(K)\,t^\star$
-- statement:
--   Let $I$ be an instance on a nonempty task set $K$ in which success on all tasks is the strongest indicator of full effort (eq. (3)). Then:
--   1. an AoN contract $t$ implements full effort if and only if its payment for success on all tasks is at least every incentive price, $t(K)\ge\theta(S)$ for every $S\subsetneq K$;
--   2. with $t^\star=\max_{S\subsetneq K}\theta(S)$,
--   $$\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}=P_K(K)\,t^\star. \tag{10}$$
--
--   Eq. (10) turns Min-Pay into a maximum of finitely many explicit numbers; it is the inequality used in the upper bound of Theorem 2.
--
--   Differences from the source:
--   - generalization: (10) is stated in §4.1.2 for independent tasks → any instance satisfying eq. (3); reason: its derivation uses only Lemma 1, i.e. eq. (3), and the paper applies (10) under (3) in §4.2 and App. D.1.1; independent tasks satisfy (3) by Observation 3, so the Lean statement specializes to the source's
--   - encoding: max over S ⊊ K → Finset.sup' over the nonempty set of deviations, with K nonempty; reason: the maximum ranges over a nonempty set exactly when K ≠ ∅
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), §4.1.2, eq. (10), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_IsAoN
import Definitions.Def_MultitaskContracts_Instance_StrongestIndicator
import Definitions.Def_MultitaskContracts_Instance_incentivePrice
import Definitions.Def_MultitaskContracts_Instance_tStar

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Eq. (10)** (§4.1.2, p.13, PDF 15). Assume eq. (3) and `K ≠ ∅`. An AoN contract implements
full effort if and only if its payment for success on all tasks is at least every incentive price
`θ(S)`, `S ⊊ K`; so the optimal payment for success on all tasks is `t⋆ := max_{S⊊K} θ(S)` and
`OPT^Bun_MinPay = P_K(K) t⋆`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), eq. (10), p.13.

**Formalization Note.** Stated under eq. (3), the hypothesis its derivation (Lemma 1) uses; the
paper applies (10) under (3) in §4.2 and App. D.1.1. `OPT^Bun_MinPay` is in `ℝ≥0∞`. -/
theorem eq_10 [Nonempty K] (I : Instance K) (h3 : I.StrongestIndicator) :
    (∀ t : Finset K → ℝ, IsAoN t →
      (I.Implements t Finset.univ ↔ ∀ S ∈ deviations K, I.incentivePrice S ≤ t Finset.univ)) ∧
    I.optMinPay (bundle K) = ENNReal.ofReal (I.P Finset.univ Finset.univ * I.tStar) := by sorry

end MultitaskContracts
