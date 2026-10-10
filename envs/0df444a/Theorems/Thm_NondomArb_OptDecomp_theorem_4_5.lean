-- Prove2me | Theorems.Thm_NondomArb_OptDecomp_theorem_4_5
-- name    : NondomArb.OptDecomp.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:16:00.41524+00:00
-- url     : https://prove2.me/theorems/2c940a93-4b97-48b1-82b8-db5fe0e7ed84
-- title:
--   Theorem 4.5 — NA(𝒫) ⟺ every N_t is 𝒫-polar ⟺ every P ∈ 𝒫 is dominated by some Q ∈ 𝒬
-- statement:
--   Consider the nondominated market of §1.2 without options ($e = 0$), with the standing assumptions on $\mathcal P_t$ and $S$, the set $\mathcal P$ of possible models, the set $\mathcal Q$ of martingale measures $Q \lll \mathcal P$, and $N_t = \{\omega \in \Omega_t : \mathrm{NA}(\mathcal P_t(\omega)) \text{ fails}\}$.
--
--   **Theorem 4.5.** The following are equivalent:
--   1. NA($\mathcal P$) holds;
--   2. $N_t$ is $\mathcal P$-polar for all $t \in \{0, \dots, T-1\}$;
--   3. for all $P \in \mathcal P$ there exists $Q \in \mathcal Q$ such that $P \ll Q$.
--
--   The equivalence of 1 and 3 is the First Fundamental Theorem of Asset Pricing for the nondominated multi-period market; the equivalence of 1 and 2 says that multi-period no-arbitrage is the same as one-period no-arbitrage at quasi every node. In the proof of the optional decomposition it is used to pass from $\mathcal Q$-polar to $\mathcal P$-polar sets: by 3, $\mathcal Q$ and $\mathcal P$ have the same polar sets.
--
--   **Formalization Note.** Stated with `List.TFAE`, as in mission I. $N_t$ is seen in $\Omega$ through the prefix map.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 20, Theorem 4.5

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_OptDecomp_Model

open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.OptDecomp

/-- **Theorem 4.5** (Bouchard–Nutz, p. 20). In the market of §1.2 without options (`e = 0`), the
following are equivalent: (i) `NA(𝒫)` holds; (ii) `N_t = {ω ∈ Ω_t : NA(𝒫_t(ω)) fails}` is
`𝒫`-polar for all `t ∈ {0, …, T − 1}`; (iii) for all `P ∈ 𝒫` there exists `Q ∈ 𝒬` such that
`P ≪ Q`. -/
theorem theorem_4_5 {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁] [MeasurableSpace Ω₁]
    [BorelSpace Ω₁] {T d : ℕ} (M : Market Ω₁ T d 0) (hM : M.Standing) :
    List.TFAE [M.NA,
      ∀ t (ht : t < T), M.IsPolar ((fun ω => NondomArb.Superhedge.pre ω t ht.le) ⁻¹' M.badSet t),
      ∀ P ∈ M.models, ∃ Q ∈ M.MartMeasures, P ≪ Q] := by sorry

end NondomArb.OptDecomp
