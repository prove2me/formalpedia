-- Prove2me | Theorems.Thm_MFGLiquidation_Nash_lemma_3_2
-- name    : MFGLiquidation.Nash.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:16.923825+00:00
-- url     : https://prove2.me/theorems/1c5f50a5-eb42-43e0-949c-f44332e8e1f3
-- title:
--   Lemma 3.2 — each player's FBSDE solution is one measurable function Φ of (𝒳ⁱ, Wⁱ, W⁰)
-- statement:
--   This is the Yamada–Watanabe-type representation of the players' equilibrium processes.
--
--   Consider the $N$-player population of the mission (players indexed $i=0,1,2,\dots$, the paper's $i=1,2,\dots$), under Assumption 3.1 and, for every player, the standing Assumption 2.3. For each player $i$ let $(X^i,Y^i,Z^i)$ be the solution of the FBSDE (2.3) associated with $(W^0,\mathcal X^i,W^i,\kappa^i,\eta^i,\lambda^i)$ in the class of Theorem 2.4. Then there is a measurable map
--   $$\Phi:\ \mathbb R\times(\mathbb R^k)^{\mathbb R_{\ge0}}\times\mathbb R^{\mathbb R_{\ge0}}\to(\mathbb R\times\mathbb R\times\mathbb R^{k+1})^{\mathbb R_{\ge0}}$$
--   that does not depend on $i$, such that for every player $i$
--   $$\Big(X^i_t,\ Y^i_t,\ \int_0^tZ^i_s\,ds\Big)=\Phi(\mathcal X^i,W^i,W^0)(t)\quad\text{a.s.},$$
--   for every $t\in[0,T]$ in the first coordinate and every $t\in[0,T)$ in the other two. In particular there is a measurable $\phi$, not depending on $i$, with
--   $$\xi^{*,i}_t=\phi(\mathcal X^i,W^0,W^i)(t)\quad\text{a.s., for every }t<T, \tag{3.1}$$
--   where $\xi^{*,i}=Y^i/(2\eta^i)$ is player $i$'s optimal control (2.2).
--
--   Since $\Phi$ and $\phi$ are the same for every player, the players' equilibrium processes are identically distributed functionals of their own data; this is what makes the $N$-player estimates of Theorem 3.3 symmetric in $i$.
--
--   **Formalization Note.** Assumption 2.3 for each player is added: it is the paper's standing assumption ("We assume throughout", p. 8), and the solution of (2.3) is unique only under it. The paper's target space $\mathcal H_\alpha\times(\mathcal C[0,T-])^2$ carries no σ-algebra; we take paths $\mathbb R_{\ge0}\to\mathbb R\times\mathbb R\times\mathbb R^{k+1}$ with the product σ-algebra, and the domain likewise. Equality is stated for each $t$ almost surely (a modification), since the solution concept carries no path regularity. The time integral $\int_0^tZ^i\,ds$ is taken coordinatewise, as printed. The argument orders $\Phi(\mathcal X^i,W^i,W^0)$ and $\phi(\mathcal X^i,W^0,W^i)$ are kept as printed. The paper only says $\phi$ is a "function"; we ask for measurability, which follows from that of $\Phi$ and Assumption 3.1.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 21–22, Lemma 3.2 and (3.1)

import Mathlib
import Definitions.Def_MFGLiquidation_Nash_Setting
import Definitions.Def_MFGLiquidation_Nash_Game
import Definitions.Def_MFGLiquidation_Nash_Players

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

theorem lemma_3_2
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (Pop : Population Ω k) (ν : Measure ℝ) (hstd : Pop.Standing P ν)
    (h31 : Pop.Assumption31)
    (h23 : ∀ i, (Pop.player i).Assumption23 P (hstd.player i))
    (Xp Yp : ℕ → ℝ≥0 → Ω → ℝ) (Zp : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hsol : ∀ i, SolvesFBSDE23InClass (hstd.player i) (Xp i) (Yp i) (Zp i)) :
    (∃ Φ : ℝ × (ℝ≥0 → Fin k → ℝ) × (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ × ℝ × (Fin (k + 1) → ℝ)),
      Measurable Φ ∧ ∀ i,
        (∀ t ≤ Pop.T, Xp i t =ᵐ[P]
          fun ω => (Φ (Pop.Xs i ω, fun s => Pop.Wp i s ω, fun s => Pop.W0 s ω) t).1) ∧
        (∀ t < Pop.T, Yp i t =ᵐ[P]
          fun ω => (Φ (Pop.Xs i ω, fun s => Pop.Wp i s ω, fun s => Pop.W0 s ω) t).2.1) ∧
        (∀ t < Pop.T, (fun ω (j : Fin (k + 1)) => ∫ s in Set.Icc (0 : ℝ) t, Zp i j s.toNNReal ω)
          =ᵐ[P] fun ω => (Φ (Pop.Xs i ω, fun s => Pop.Wp i s ω, fun s => Pop.W0 s ω) t).2.2)) ∧
    (∃ φ : ℝ × (ℝ≥0 → ℝ) × (ℝ≥0 → Fin k → ℝ) → (ℝ≥0 → ℝ),
      Measurable φ ∧ ∀ i, ∀ t < Pop.T, Pop.xiStar Yp i t =ᵐ[P]
        fun ω => φ (Pop.Xs i ω, fun s => Pop.W0 s ω, fun s => Pop.Wp i s ω) t) := by sorry

end MFGLiquidation.Nash
