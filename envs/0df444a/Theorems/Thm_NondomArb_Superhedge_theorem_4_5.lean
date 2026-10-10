-- Prove2me | Theorems.Thm_NondomArb_Superhedge_theorem_4_5
-- name    : NondomArb.Superhedge.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:14.746325+00:00
-- url     : https://prove2.me/theorems/a9a8d92b-9cd7-4a12-a847-447ffba900d9
-- title:
--   Theorem 4.5 — without options: NA(𝒫) ⟺ every N_t is 𝒫-polar ⟺ every P ∈ 𝒫 is dominated by some Q ∈ 𝒬
-- statement:
--   Consider the multi-period market of §1.2 without options ($e=0$), with martingale measures $\mathcal Q=\{Q\lll\mathcal P: S\text{ is a }Q\text{-martingale}\}$.
--
--   **Theorem.** The following are equivalent:
--   1. NA($\mathcal P$) holds;
--   2. $N_t=\{\omega\in\Omega_t:\mathrm{NA}(\mathcal P_t(\omega))\text{ fails}\}$ is $\mathcal P$-polar for all $t\in\{0,\dots,T-1\}$;
--   3. for all $P\in\mathcal P$ there exists $Q\in\mathcal Q$ such that $P\ll Q$.
--
--   This is the first fundamental theorem of asset pricing in the nondominated multi-period market, together with its local (one-period) characterization.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 20, Theorem 4.5

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_Model
open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.Superhedge

/-- **Theorem 4.5** (p. 20). (No options, `e = 0`.) The following are equivalent:
(i) NA(𝒫); (ii) each `N_t`, `t = 0, …, T − 1`, is `𝒫`-polar; (iii) every `P ∈ 𝒫` is absolutely
continuous with respect to some `Q ∈ 𝒬`. -/
theorem theorem_4_5 {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁]
    [MeasurableSpace Ω₁] [BorelSpace Ω₁] {T d : ℕ}
    (M : Market Ω₁ T d 0) (hM : M.Standing) :
    List.TFAE [M.NA,
      ∀ t (ht : t < T), M.IsPolar ((fun ω => pre ω t ht.le) ⁻¹' M.badSet t),
      ∀ P ∈ M.models, ∃ Q ∈ M.MartMeasures, P ≪ Q] := by sorry

end NondomArb.Superhedge
