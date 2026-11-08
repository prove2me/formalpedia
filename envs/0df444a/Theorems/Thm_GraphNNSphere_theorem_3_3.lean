-- Prove2me | Theorems.Thm_GraphNNSphere_theorem_3_3
-- name    : GraphNNSphere.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:44:02.047457+00:00
-- url     : https://prove2.me/theorems/d1f46a5a-6fbb-4feb-97d0-94184815fc31
-- title:
--   Theorem 3.3 — traps in a rank window
-- statement:
--   Let $T>k$ and $L$ be positive integers and let $\rho\in(0,\pi/2)$ be the distance cutoff. Define $\vartheta$ by $nF(\vartheta)=T$, and put $I=I_\vartheta(\rho)$ and $J=J_\vartheta(\rho)$. Suppose that
--   $$T\ge e^{c_{\mathrm{trap}}d},\quad dJ\ge\log T+c_{\mathrm{trap}}d,\quad dI\ge\log L+c_{\mathrm{trap}}d,$$
--   and that $\vartheta\le\pi/2-\varepsilon$, $\varepsilon\vartheta\le\rho<r^*(\vartheta)$ and $\cot\vartheta\tan(\rho/2)\le1-\varepsilon$, for fixed $c_{\mathrm{trap}},\varepsilon>0$.
--
--   For all sufficiently large $n$, with probability at least $1-e^{-c_{\mathrm{trap}}d/4}$ over the uniform data set, simultaneously for every navigation graph $G$ constructed from the data, there is a measurable query set $Q_G$ with $\sigma_{d-1}(Q_G)\ge1-e^{-c_{\mathrm{trap}}d/8}$ such that, for every $q\in Q_G$, at least $(1-e^{-c_{\mathrm{trap}}d/8})T$ entries $x_0$ of rank in $[T,2T)$ satisfy $W_G(q;x_0)\ge L$. The same entries can be chosen so that each either has $d_G(x_0)>L$ or is a failing entry with $W_G(q;x_0)=\infty$.
--
--   This is the engine of the lower bound: it applies to every graph, however it is chosen after seeing the data.
--
--   Differences from the source:
--   - reading: "for all sufficiently large n" → hypotheses holding eventually in n for sequences d, T, L, ρ under the standing assumptions of §2.1, with the threshold depending on the sequences; reason: the convention of §2.1
--   - encoding: "with probability at least" → an explicit measurable data event E, chosen before G; reason: "simultaneously for every navigation graph"
--   - encoding: "the same entries can be chosen" → one count of entries satisfying all clauses together; reason: the two sentences of the conclusion
--   - encoding: ϑ defined by nF(ϑ) = T → capRadius d (T/n); reason: the infimum encoding; T > n gives the value 0, which ρ < r*(ϑ) excludes, as r*(0) = 0
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 3.3, p.23

import Mathlib
import Definitions.Def_GraphNNSphere_capRadius
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_StandingAsymp
import Definitions.Def_GraphNNSphere_Jrate
import Definitions.Def_GraphNNSphere_Irate
import Definitions.Def_GraphNNSphere_rStar
import Definitions.Def_GraphNNSphere_IsNavGraph
import Definitions.Def_GraphNNSphere_W
import Definitions.Def_GraphNNSphere_rank

open MeasureTheory Filter

namespace GraphNNSphere

open Classical in
/-- Theorem 3.3, traps in a rank window (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on
the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 3.3, p.23).

**Formalization Note** `T`, `L`, `ρ` are sequences, and the hypotheses hold eventually in `n`, the
paper's "for all sufficiently large `n`". `ϑ = capRadius d (T/n)` is the solution of `n F(ϑ) = T`.
The data event `E` comes before `G`, and the query set `Q_G` after `G`. One count carries both
sentences of the conclusion: the same entries have `W ≥ L`, and each has `d_G(x₀) > L` or
`W = ∞`. -/
theorem theorem_3_3 (k : ℕ) (hk : 1 ≤ k) (ctrap ε : ℝ) (hctrap : 0 < ctrap) (hε : 0 < ε)
    (d : ℕ → ℕ) (hd : StandingAsymp d) (T L : ℕ → ℕ) (ρ : ℕ → ℝ)
    (hyp : ∀ᶠ n : ℕ in atTop,
      let ϑ : ℝ := capRadius (d n) ((T n : ℝ) / (n : ℝ))
      k < T n ∧ 1 ≤ L n ∧ 0 < ρ n ∧ ρ n < Real.pi / 2 ∧
      Real.exp (ctrap * (d n : ℝ)) ≤ (T n : ℝ) ∧
      Real.log (T n : ℝ) + ctrap * (d n : ℝ) ≤ (d n : ℝ) * Jrate ϑ (ρ n) ∧
      Real.log (L n : ℝ) + ctrap * (d n : ℝ) ≤ (d n : ℝ) * Irate ϑ (ρ n) ∧
      ϑ ≤ Real.pi / 2 - ε ∧ ε * ϑ ≤ ρ n ∧ ρ n < rStar ϑ ∧
      Real.cot ϑ * Real.tan (ρ n / 2) ≤ 1 - ε) :
    ∀ᶠ n : ℕ in atTop,
      ∃ E : Set (Fin n → Sph (d n)), MeasurableSet E ∧
        1 - Real.exp (-(ctrap * (d n : ℝ) / 4)) ≤ (dataLaw n (d n) E).toReal ∧
        ∀ X ∈ E, ∀ G : NavGraph n, IsNavGraph G →
          ∃ QG : Set (Sph (d n)), MeasurableSet QG ∧
            1 - Real.exp (-(ctrap * (d n : ℝ) / 8)) ≤ (unif (d n) QG).toReal ∧
            ∀ q ∈ QG, (1 - Real.exp (-(ctrap * (d n : ℝ) / 8))) * (T n : ℝ) ≤
              ((Finset.univ.filter (fun x₀ : Fin n =>
                T n ≤ rank X q x₀ ∧ rank X q x₀ < 2 * T n ∧
                (L n : ℕ∞) ≤ W G X q k x₀ ∧
                (L n < (G x₀).card ∨ W G X q k x₀ = ⊤))).card : ℝ) := by sorry

end GraphNNSphere
