-- Prove2me | Theorems.Thm_MultitaskContracts_lemma_1
-- name    : MultitaskContracts.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:33:29.755105+00:00
-- url     : https://prove2.me/theorems/40e29cd2-bfd3-4020-9ed8-6f2487872de8
-- title:
--   Lemma 1 — under (3) some optimal Min-Pay contract is all-or-nothing
-- statement:
--   Let $I$ be an instance of the multitask model in which success on all tasks is the strongest indicator of full effort, $P_K(K)P_S(Y)\ge P_K(Y)P_S(K)$ for all $S,Y$ (eq. (3)). Then there is an optimal Min-Pay contract that is AoN: a contract $t$ with $t(Y)\ge0$ for all $Y$ and $t(Y)=0$ for $Y\subsetneq K$ that implements full effort and satisfies
--   $$\mathbb E_{Y\sim P_K}[t(Y)]=\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}.$$
--
--   It reduces Min-Pay over bundle contracts to the choice of the single payment $t(K)$.
--
--   Differences from the source:
--   - encoding: OPT^Bun_MinPay (a limit of minima, ∞ when infeasible) → ℝ≥0∞ value (infimum over B ≥ 0 of the infimum over feasible contracts); reason: same value
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Lemma 1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_IsAoN
import Definitions.Def_MultitaskContracts_Instance_StrongestIndicator

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Lemma 1** (p.12, PDF 14). If success on all tasks is the strongest indicator of full effort
(eq. (3)), there is an optimal Min-Pay contract that is AoN.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Lemma 1, p.12.

**Formalization Note.** "Optimal Min-Pay contract": a bundle contract implementing `K` whose
expected payment under full effort equals `OPT^Bun_MinPay` (in `ℝ≥0∞`); `IsAoN` includes
membership in the bundle class. -/
theorem lemma_1 (I : Instance K) (h3 : I.StrongestIndicator) :
    ∃ t, IsAoN t ∧ I.Implements t Finset.univ ∧
      ENNReal.ofReal (I.expect Finset.univ t) = I.optMinPay (bundle K) := by sorry

end MultitaskContracts
