-- Prove2me | Theorems.Thm_NondomArb_OptDecomp_theorem_6_1
-- name    : NondomArb.OptDecomp.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:18:56.062992+00:00
-- url     : https://prove2.me/theorems/34aa72f0-edf9-49f0-a252-efaa67a26451
-- title:
--   Theorem 6.1 — nondominated optional decomposition: a supermartingale under every Q ∈ 𝒬 is V₀ + H • S − K
-- statement:
--   Consider the nondominated discrete-time market of Bouchard and Nutz without options ($e = 0$): a Polish space $\Omega_1$, paths in $\Omega = \Omega_1^T$ with the filtration $\mathcal F_t$ given by the universal completion of $\mathcal B(\Omega_1^t)$, one-period model sets $\mathcal P_t(\omega)$ (nonempty, convex, with analytic graph), Borel stock prices $S_t : \Omega_1^t \to \mathbb R^d$, the set $\mathcal P$ of possible models, the predictable strategies $\mathcal H$, and the set $\mathcal Q$ of martingale measures $Q \lll \mathcal P$.
--
--   **Theorem 6.1.** Let NA($\mathcal P$) hold, and let $V$ be an adapted process such that $V_t$ is upper semianalytic and in $L^1(Q)$ for all $Q \in \mathcal Q$ and $t \in \{1, 2, \dots, T\}$. The following are equivalent:
--   1. $V$ is a supermartingale under each $Q \in \mathcal Q$;
--   2. there exist $H \in \mathcal H$ and an adapted increasing process $K$ with $K_0 = 0$ such that
--   $$V_t = V_0 + H \bullet S_t - K_t \quad \mathcal P\text{-q.s.}, \qquad t \in \{0, 1, \dots, T\}.$$
--
--   This is a nondominated version of the Optional Decomposition Theorem of El Karoui–Quenez and Kramkov, in discrete time. With a single model it reduces to the classical statement; here the decomposition holds simultaneously under every model in $\mathcal P$, with one strategy $H$ and one increasing process $K$, even though the measures in $\mathcal P$ need not be dominated by a single reference measure.
--
--   **Formalization Note.** A process is a family of functions `V t` on $\Omega_1^t$, so adaptedness is built into the type, and $\mathcal F_t$-measurability is universal measurability. Upper semianalyticity and $Q$-integrability are assumed for $t \ge 1$, as printed ($V_0$ is a constant). The increasing process $K$ is required to be nondecreasing on every path; this gives the same theorem as the quasi-sure reading, by passing to the running maximum. The Lean strategy `H u` is the paper's $H_{u+1}$, and $H \bullet S_t$ is the wealth at time $t$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, pp. 33–34, §6, Theorem 6.1

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_OptDecomp_Model
import Definitions.Def_NondomArb_OptDecomp_Process

open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.OptDecomp

/-- **Theorem 6.1** (Bouchard–Nutz, pp. 33–34), nondominated optional decomposition. In the
market of §1.2 without options (`e = 0`), let `NA(𝒫)` hold, and let `V` be an adapted process
such that `V_t` is upper semianalytic and in `L¹(Q)` for all `Q ∈ 𝒬` and `t ∈ {1, …, T}`.
The following are equivalent:
(i) `V` is a supermartingale under each `Q ∈ 𝒬`;
(ii) there exist `H ∈ ℋ` and an adapted increasing process `K` with `K_0 = 0` such that
`V_t = V_0 + H • S_t − K_t` `𝒫`-q.s., `t ∈ {0, 1, …, T}`. -/
theorem theorem_6_1 {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁] [MeasurableSpace Ω₁]
    [BorelSpace Ω₁] {T d : ℕ} (M : Market Ω₁ T d 0) (hM : M.Standing) (hNA : M.NA)
    (V : (t : ℕ) → (Fin t → Ω₁) → ℝ) (hV : M.Adapted V)
    (hVusa : ∀ t, 1 ≤ t → t ≤ T → NondomArb.Superhedge.IsUpperSemianalytic (fun ω : Fin t → Ω₁ => ((V t ω : ℝ) : EReal)))
    (hVint : ∀ Q ∈ M.MartMeasures, ∀ t (ht1 : 1 ≤ t) (ht : t ≤ T),
      Integrable (fun ω => V t (NondomArb.Superhedge.pre ω t ht)) Q) :
    (∀ Q ∈ M.MartMeasures, M.IsSupermartingale V Q) ↔
      ∃ H, M.Admissible H ∧ ∃ K : (t : ℕ) → (Fin t → Ω₁) → ℝ, M.IsAdaptedIncreasing K ∧
        (∀ ω, K 0 ω = 0) ∧
        ∀ t (ht : t ≤ T), M.QS (fun ω =>
          V t (NondomArb.Superhedge.pre ω t ht) = V 0 (NondomArb.Superhedge.pre ω 0 (Nat.zero_le T)) + M.gainAt H t (NondomArb.Superhedge.pre ω t ht)
            - K t (NondomArb.Superhedge.pre ω t ht)) := by sorry

end NondomArb.OptDecomp
