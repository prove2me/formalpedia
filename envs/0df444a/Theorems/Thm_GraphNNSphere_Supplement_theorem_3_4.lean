-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_3_4
-- name    : GraphNNSphere.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:50:09.713769+00:00
-- url     : https://prove2.me/theorems/85b88bba-d2a6-468f-8955-d8ccd0b873f1
-- title:
--   Theorem 3.4, p.26 — degree and evaluation-cost lower bounds $(\Delta^*)^{1-o(1)}$
-- statement:
--   Let the data $D_n$ be $n$ independent uniform points on $S^{d-1}$, either in the logarithmic regime $d=\lfloor c\log n\rfloor$ or in the dense regime $\sqrt{\log n}\ll d\ll\log n$, and fix $k\ge1$. Let $\Delta^*=nF_{d-1}(\rho^*)$, $\cos\rho^*=\cos^2\theta_1$, be the critical degree of (1). With probability $1-o(1)$ over $D_n$ the following holds simultaneously for every $0\le\varepsilon<1$ and every navigation graph $G$. If $G$ succeeds from every entry for every query in a measurable set $S_G$ with $\sigma_{d-1}(S_G)\ge1-\varepsilon$, then
--
--   1. all but $(\varepsilon+o(1))n$ data points have degree $|G(x)|\ge(\Delta^*)^{1-o(1)}$;
--   2. the average degree satisfies $\frac1n\sum_x|G(x)|\ge(1-\varepsilon-o(1))(\Delta^*)^{1-o(1)}$;
--   3. for every query $q\in S_G$ outside a set of surface measure $o(1)$, all but an $(\varepsilon+o(1))$ fraction of entries $x_0$ satisfy $W_G(q;x_0)\ge(\Delta^*)^{1-o(1)}$.
--
--   The $o(1)$ terms do not depend on $\varepsilon$ or $G$, so the conclusion also holds for $\varepsilon=\varepsilon_n\to0$. Taking $\varepsilon=o(1)$ shows that any graph succeeding from every entry for most uniform queries has average degree and entry-averaged evaluation cost at least the critical scale, completing the uniform critical curve together with Theorem 3.1(a).
--
--   **Formalization Note** The four $o(1)$ terms are explicit sequences tending to $0$, chosen before $n$; the data event is chosen before $\varepsilon$ and $G$.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - generalization: "Fix 0 ≤ ε < 1", with probability 1 − o(1), and "the conclusion also holds for ε = ε_n → 0" → one data event and one set of o(1) sequences, chosen before ε and G, serve every 0 ≤ ε < 1 simultaneously; reason: the proof gives the bounds "simultaneously for every graph and uniformly in 0 ≤ ε < 1" (p.27); fixing ε (or a sequence ε_n) recovers the source
--   - encoding: degree at least (Δ*)^{1−o(1)} for all but (ε + o(1))n points → #{x : |G(x)| < (Δ*)^{1−e_n}} ≤ (ε + b_n)n; reason: same condition
--   - encoding: W_G(q; x₀) ≥ (Δ*)^{1−o(1)} for all but an (ε + o(1)) fraction of entries → #{x₀ : W finite and < (Δ*)^{1−e_n}} ≤ (ε + b_n)n; reason: a failing entry has W = ∞, which satisfies the bound
--   - encoding: measurable / Borel query sets → MeasurableSet on the sphere (the subtype of ℝ^d with its Borel σ-algebra); reason: same sets
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 3.4, p.26 (PDF p.28); Δ* from Eq. (1), p.3

import Mathlib
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_IsNavGraph
import Definitions.Def_GraphNNSphere_W
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_IsDenseRegime
import Definitions.Def_GraphNNSphere_Supplement_critDeg

open MeasureTheory Filter Topology

namespace GraphNNSphere

namespace Supplement

open Classical in
/-- Theorem 3.4, degree and evaluation-cost lower bounds (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 3.4, p.26). For uniform
data in the logarithmic regime (first conjunct) and in the dense regime (second conjunct), with
probability `1 - o(1)`, every navigation graph `G` that succeeds from every entry on a measurable
query set `S_G` with `σ(S_G) ≥ 1 - ε` has all but `(ε + o(1))n` points of degree at least
`(Δ*)^{1-o(1)}`, average degree at least `(1 - ε - o(1))(Δ*)^{1-o(1)}`, and, for every query of `S_G`
outside a set of surface measure `o(1)`, all but an `(ε + o(1))` fraction of entries satisfy
`W_G(q; x₀) ≥ (Δ*)^{1-o(1)}`.

**Formalization Note** The four `o(1)` terms are explicit sequences `a, b, e, s → 0` chosen before
`n`. The data event comes before `ε` and `G`, so one event serves all `0 ≤ ε < 1` and all graphs, and
the sequences do not depend on `ε`; this covers `ε = ε_n → 0`. `Δ* = n F(ρ*)` is `critDeg`. A
failing entry has `W = ⊤`, so `W < (Δ*)^{1-e_n}` means a finite value below the bound. -/
theorem theorem_3_4 :
    (∀ k : ℕ, 1 ≤ k → ∀ c : ℝ, 0 < c →
      ∃ a b e s : ℕ → ℝ, Tendsto a atTop (𝓝 0) ∧ Tendsto b atTop (𝓝 0) ∧
        Tendsto e atTop (𝓝 0) ∧ Tendsto s atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ Ev : Set (Fin n → Sph (logDim c n)), MeasurableSet Ev ∧
          1 - a n ≤ (dataLaw n (logDim c n) Ev).toReal ∧
          ∀ X ∈ Ev, ∀ ε : ℝ, 0 ≤ ε → ε < 1 → ∀ G : NavGraph n, IsNavGraph G →
          ∀ S : Set (Sph (logDim c n)), MeasurableSet S →
            1 - ε ≤ (unif (logDim c n) S).toReal →
            (∀ q ∈ S, ∀ x₀ : Fin n, W G X q k x₀ < ⊤) →
            ((Finset.univ.filter (fun x : Fin n =>
                ((G x).card : ℝ) < critDeg n (logDim c n) ^ (1 - e n))).card : ℝ) ≤
                (ε + b n) * n ∧
            (1 - ε - b n) * critDeg n (logDim c n) ^ (1 - e n) ≤
                (∑ x : Fin n, ((G x).card : ℝ)) / n ∧
            ∃ Z : Set (Sph (logDim c n)), MeasurableSet Z ∧ (unif (logDim c n) Z).toReal ≤ s n ∧
              ∀ q ∈ S \ Z,
                ((Finset.univ.filter (fun x₀ : Fin n => ∃ m : ℕ, W G X q k x₀ = m ∧
                    (m : ℝ) < critDeg n (logDim c n) ^ (1 - e n))).card : ℝ) ≤ (ε + b n) * n) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ d : ℕ → ℕ, IsDenseRegime d →
      ∃ a b e s : ℕ → ℝ, Tendsto a atTop (𝓝 0) ∧ Tendsto b atTop (𝓝 0) ∧
        Tendsto e atTop (𝓝 0) ∧ Tendsto s atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ Ev : Set (Fin n → Sph (d n)), MeasurableSet Ev ∧
          1 - a n ≤ (dataLaw n (d n) Ev).toReal ∧
          ∀ X ∈ Ev, ∀ ε : ℝ, 0 ≤ ε → ε < 1 → ∀ G : NavGraph n, IsNavGraph G →
          ∀ S : Set (Sph (d n)), MeasurableSet S → 1 - ε ≤ (unif (d n) S).toReal →
            (∀ q ∈ S, ∀ x₀ : Fin n, W G X q k x₀ < ⊤) →
            ((Finset.univ.filter (fun x : Fin n =>
                ((G x).card : ℝ) < critDeg n (d n) ^ (1 - e n))).card : ℝ) ≤ (ε + b n) * n ∧
            (1 - ε - b n) * critDeg n (d n) ^ (1 - e n) ≤ (∑ x : Fin n, ((G x).card : ℝ)) / n ∧
            ∃ Z : Set (Sph (d n)), MeasurableSet Z ∧ (unif (d n) Z).toReal ≤ s n ∧
              ∀ q ∈ S \ Z,
                ((Finset.univ.filter (fun x₀ : Fin n => ∃ m : ℕ, W G X q k x₀ = m ∧
                    (m : ℝ) < critDeg n (d n) ^ (1 - e n))).card : ℝ) ≤ (ε + b n) * n) := by sorry

end Supplement

end GraphNNSphere
