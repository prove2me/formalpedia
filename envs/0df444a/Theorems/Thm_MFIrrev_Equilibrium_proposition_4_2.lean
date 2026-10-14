-- Prove2me | Theorems.Thm_MFIrrev_Equilibrium_proposition_4_2
-- name    : MFIrrev.Equilibrium.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:23.057462+00:00
-- url     : https://prove2.me/theorems/6d270690-9a89-4191-8a54-cce84cd36e42
-- title:
--   Proposition 4.2 (corrected), pp. 15–16 — the stopping problem (4.13) has threshold regions, a C¹ value with (4.17), and the hitting time is optimal
-- statement:
--   Assume the standing conditions of §2 and Assumption 2.1, and fix $Q\in(0,\infty)^2$. Let $v$ be the value function (4.13) of the optimal stopping problem, $\eta_i=\varphi_i+\zeta_iQ_i^{-\alpha}$, and let $\mathcal C_i=\{x>0: v(x,i)<\kappa\}$, $\mathcal S_i=\{x>0:v(x,i)\ge\kappa\}$ be the sections of the continuation and stopping regions (4.16). Then there exist $a_1,a_2\ge0$ such that:
--
--   1. $\mathcal C_i=\{x>0: x>a_i\}$ and $\mathcal S_i=\{x>0: x\le a_i\}$;
--   2. $v(\cdot,i)\in C^1((0,\infty))$, $v(\cdot,i)\in C^2((a_i,\infty))$, and $v''(\cdot,i)$ is bounded on every compact subset of $(0,\infty)$ (away from the point $a_i$), and
--   $$\begin{cases}(\bar{\mathcal L}-(\rho+\delta))v(x,i)+\eta_i-2cx\ge0,& 0<x<a_i,\\ (\bar{\mathcal L}-(\rho+\delta))v(x,i)+\eta_i-2cx=0,& x>a_i,\\ \kappa-v(x,i)=0,& 0<x\le a_i,\\ \kappa-v(x,i)\ge0,& x>a_i;\end{cases}$$
--   3. for every $x>0$ and $i$, $\tau^\star=\inf\{t\ge0:\bar X_t\le a_{\varepsilon_t}\}$ is an $\mathbb F$-stopping time and is optimal for (4.13) under $\bar{\mathbb P}_{(x,i)}$.
--
--   This identifies the free boundaries $a_i$ that become the investment barriers of the singular control problem.
--
--   **Formalization Note (correction).** The page prints $\mathcal C_i=\{x<a_i\}$, $\mathcal S_i=\{x\ge a_i\}$ and the last two lines of (4.17) with $x<a_i$ and $x\ge a_i$. These are swapped: stopping at once gives $v\le\kappa$, item 3 stops on $\{\bar X\le a_\varepsilon\}$, p. 16 says $v(x,1)=\kappa=v(x,2)$ for $x\in(0,a_1)$, and Step 1 of the proof of Theorem 4.1 sets $a_i(Q)=\inf\{x>0:v^Q(x,i)<\kappa\}$. The statement above is the corrected one; the two differential lines of (4.17) are as printed. Regimes are `Fin 2` (index `0` = regime 1). $C^1(\mathbb R_+)$ is read on $(0,\infty)$, the domain of $v$; $v''\in L^\infty_{loc}$ is stated as a bound on compacts of $(0,\infty)$ at every point other than $a_i$, where $v''$ may jump.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, pp. 15–16, Proposition 4.2 with (4.13)–(4.17) (regions corrected); proof in Appendix A

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_StoppingProblem

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MFIrrev.Equilibrium

/-- Proposition 4.2 (corrected), Aïd–Basei–Ferrari pp. 15–16. Regime index `0` is the paper's regime 1.
The value function `v` of the stopping problem (4.13) has thresholds `a_j ≥ 0` such that
(i) the continuation region is `{x > a_j}` and the stopping region `{x ≤ a_j}` (the page prints
them swapped); (ii) `v(·, j)` is `C¹` on `(0, ∞)`, `C²` on `(a_j, ∞)`, with `v''` locally bounded;
(4.17) with the obstacle lines corrected; (iii) the hitting time of `{X̄_t ≤ a_{ε_t}}` is an optimal
stopping time. -/
theorem proposition_4_2 (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j) (hp : ∀ j, 0 < m.p j ∧ m.p j < 1)
    (hρ : 0 < m.ρ) (hc : 0 < m.c) (hκ : 0 < m.κ) (hφ : ∀ j, 0 < m.φ j) (hζ : ∀ j, 0 < m.ζ j)
    (hα0 : 0 < m.α) (hα1 : m.α < 1) (hφρδ : ∀ j, m.ρ + m.δ < m.φ j)
    (hA21 : 2 * max (m.σ 0 ^ 2) (m.σ 1 ^ 2) < m.ρ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Setting Ω) (hS : IsSetting m P S)
    (Q : Fin 2 → ℝ) (hQ : ∀ j, 0 < Q j) :
    ∃ a : Fin 2 → ℝ, (∀ j, 0 ≤ a j) ∧
      -- (i) corrected: 𝒞_j = {y > a_j}, 𝒮_j = {y ≤ a_j}
      (∀ j, ∀ y : ℝ, 0 < y → (vStop m P S Q y j < m.κ ↔ a j < y)) ∧
      -- (ii) regularity
      (∀ j, ContDiffOn ℝ 1 (fun y => vStop m P S Q y j) (Ioi 0)) ∧
      (∀ j, ContDiffOn ℝ 2 (fun y => vStop m P S Q y j) (Ioi (a j))) ∧
      (∀ j, ∀ K : Set ℝ, IsCompact K → K ⊆ Ioi 0 → ∃ C : ℝ, ∀ y ∈ K, y ≠ a j →
        |deriv (deriv fun z => vStop m P S Q z j) y| ≤ C) ∧
      -- (4.17), obstacle lines corrected
      (∀ j, ∀ y : ℝ, 0 < y → y < a j →
        genLbar m (fun z k => vStop m P S Q z k) y j - (m.ρ + m.δ) * vStop m P S Q y j
          + eta m Q j - 2 * m.c * y ≥ 0) ∧
      (∀ j, ∀ y : ℝ, a j < y →
        genLbar m (fun z k => vStop m P S Q z k) y j - (m.ρ + m.δ) * vStop m P S Q y j
          + eta m Q j - 2 * m.c * y = 0) ∧
      (∀ j, ∀ y : ℝ, 0 < y → y ≤ a j → m.κ - vStop m P S Q y j = 0) ∧
      (∀ j, ∀ y : ℝ, a j < y → m.κ - vStop m P S Q y j ≥ 0) ∧
      -- (iii) optimality of the hitting time
      (∀ x : ℝ, 0 < x → ∀ i : Fin 2,
        IsStoppingTime S.ℱ (hitTime m S a x) ∧
        ∫ ω, stopPayoff m S Q x (hitTime m S a x) ω ∂(Pcond P S i) = vStop m P S Q x i) := by sorry

end MFIrrev.Equilibrium
