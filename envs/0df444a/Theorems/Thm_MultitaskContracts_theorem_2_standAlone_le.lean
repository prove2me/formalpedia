-- Prove2me | Theorems.Thm_MultitaskContracts_theorem_2_standAlone_le
-- name    : MultitaskContracts.theorem_2_standAlone_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:34:26.937957+00:00
-- url     : https://prove2.me/theorems/2b294b13-6bb4-41ec-854d-a2a2ae405295
-- title:
--   Proof of Theorem 2, upper bound — $c_k/(1-q_k/p_k)=P_K(K)\theta(K\setminus\{k\})\le P_K(K)t^\star=\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}$
-- statement:
--   Let $I$ be an instance with independent tasks on a nonempty task set $K$. For every task $k$, the stand-alone payment of $k$ satisfies
--   $$\frac{c_k}{1-q_k/p_k}=P_K(K)\,\theta(K\setminus\{k\})\ \le\ P_K(K)\,t^\star=\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}},$$
--   where $\theta$ is the incentive price and $t^\star=\max_{S\subsetneq K}\theta(S)$.
--
--   Summed over the tasks, together with Lemma 15 this gives $\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinPay}}\le|K|\cdot\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}$, the upper bound of Theorem 2.
--
--   Differences from the source:
--   - encoding: OPT^Bun_MinPay → ℝ≥0∞ value, compared with ofReal(P_K(K) t⋆); reason: same value
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), proof of Theorem 2, upper bound, display "c_k/(1 − q_k/p_k) = P_K(K) θ(K ∖ {k}) ≤ P_K(K) t⋆ = OPT^Bun_MinPay", p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_Instance_IsIndependent
import Definitions.Def_MultitaskContracts_Instance_incentivePrice
import Definitions.Def_MultitaskContracts_Instance_tStar
import Definitions.Def_MultitaskContracts_Instance_standAlone

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Upper-bound display in the proof of Theorem 2** (§4.1.3, p.15, PDF 17). For independent tasks
(`K ≠ ∅`), the stand-alone payment of every task `k` (Definition 4) satisfies
`c_k/(1 − q_k/p_k) = P_K(K) θ(K ∖ {k}) ≤ P_K(K) t⋆ = OPT^Bun_MinPay`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), proof of Theorem 2, p.15.

**Formalization Note.** `K ∖ {k}` is `Finset.univ.erase k`; `OPT^Bun_MinPay` is in `ℝ≥0∞`. -/
theorem theorem_2_standAlone_le [Nonempty K] (I : Instance K) (hind : I.IsIndependent) (k : K) :
    I.standAlone k = I.P Finset.univ Finset.univ * I.incentivePrice (Finset.univ.erase k) ∧
    I.P Finset.univ Finset.univ * I.incentivePrice (Finset.univ.erase k) ≤
      I.P Finset.univ Finset.univ * I.tStar ∧
    ENNReal.ofReal (I.P Finset.univ Finset.univ * I.tStar) = I.optMinPay (bundle K) := by sorry

end MultitaskContracts
