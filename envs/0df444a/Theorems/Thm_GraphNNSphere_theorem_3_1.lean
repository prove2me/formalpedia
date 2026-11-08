-- Prove2me | Theorems.Thm_GraphNNSphere_theorem_3_1
-- name    : GraphNNSphere.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:44:45.558715+00:00
-- url     : https://prove2.me/theorems/a967b0b5-605b-48ed-8217-e446c6ab5129
-- title:
--   Theorem 3.1 — the uniform critical degree
-- statement:
--   For uniform data on $S^{d-1}$, fix $k\ge1$. In the logarithmic regime $d=\lfloor c\log n\rfloor$, let $\Delta=\lceil n^\beta\rceil$ with fixed $0<\beta<1$. In the dense regime $\sqrt{\log n}\ll d\ll\log n$, let $\Delta=\lceil e^{\gamma d}\rceil$ with fixed $\gamma>0$. Write $\beta^*(c)=\frac c2\log(2-e^{-2/c})$ and $\gamma_c=\frac12\log2$.
--
--   **(a) Above the critical degree.** Fix an absolutely continuous query distribution $Q$ before drawing the data.
--
--   1. In the logarithmic regime, suppose $\beta>\beta^*(c)$ and choose $\beta'\in(\beta^*(c),\beta)$. There is $\eta>0$ such that, with probability at least $1-n^{-\eta}$ over $D_n$, there is a measurable set $Q_D\subseteq S^{d-1}$ with $P_{q\sim Q}(q\in Q_D)\ge1-n^{-\eta}$ on which every graph $G$ containing $G_{\rho_{\beta'}}$ and satisfying $\Delta(G)\le2\Delta$ succeeds from every entry. Each search uses $O(1)$ moves and has evaluation cost at most $\Delta^{1+o(1)}$.
--   2. In the dense regime, suppose $\gamma>\gamma_c$ and choose $\gamma'\in(\gamma_c,\gamma)$. There are $c_1,c_2>0$ such that, with probability at least $1-e^{-c_1d}$ over $D_n$, there is a measurable $Q_D$ with $P_{q\sim Q}(q\in Q_D)\ge1-e^{-c_2d}$ on which every graph $G$ containing $G_{r_{\gamma'}}$ and satisfying $\Delta(G)\le2\Delta$ succeeds from every entry. Each search uses $O(1/\theta_1)=e^{o(d)}$ moves and has evaluation cost at most $\Delta^{1+o(1)}$.
--
--   The same data events, query sets and bounds also apply to $G_{\rho_\beta}$ in the logarithmic regime, $G_{r_\gamma}$ in the dense regime, and $N_\Delta$ in both.
--
--   **(b) Below the critical degree.**
--
--   1. In the logarithmic regime, suppose $\beta<\beta^*(c)$. There are $a,\eta>0$ such that, with probability at least $1-n^{-\eta}$ over $D_n$, every navigation graph $G$ constructed from the sample admits a measurable set $Q_G$ with $\sigma_{d-1}(Q_G)\ge1-n^{-\eta}$ such that, for every $q\in Q_G$, at least $(1-o(1))n^a$ entries $x_0$ satisfy $W_G(q;x_0)\ge\Delta$.
--   2. In the dense regime, suppose $\gamma<\gamma_c$. There are $a,c_1,c_2>0$ such that, with probability at least $1-e^{-c_1d}$ over $D_n$, every navigation graph $G$ constructed from the sample admits a measurable $Q_G$ with $\sigma_{d-1}(Q_G)\ge1-e^{-c_2d}$ such that, for every $q\in Q_G$, at least $(1-o(1))e^{ad}$ entries $x_0$ satisfy $W_G(q;x_0)\ge\Delta$.
--
--   If $\Delta(G)\le\Delta$, then for every $q\in Q_G$ greedy navigation fails from at least $(1-o(1))n^a$ entries in the logarithmic regime and at least $(1-o(1))e^{ad}$ entries in the dense regime.
--
--   This is the sharp threshold of exact greedy nearest-neighbor search from every entry on uniform spherical data: above the critical degree, the threshold and nearest-neighbor graphs succeed; below it, no graph does, even one designed after seeing the sample.
--
--   Differences from the source:
--   - reading: constants and "for all large n", with d(·) and Q fixed → order: fixed parameters; then η, H, c₁, c₂, C, a; then d(·) with its regime; then the vanishing sequences; then ∀ᶠ n; then Q; then the data event; then the sample; then graphs, queries and entries; reason: §2.1: constants depend on k, c and the fixed exponents, and only the threshold depends on d(·); this is the stronger reading, and the proofs give it
--   - encoding: "with probability at least"; P(q ∈ Q_D) ≥ … → explicit measurable sets with the measure bound, and the claim for each element; reason: so that no outer measure is involved
--   - encoding: O(1), O(1/θ₁) = e^{o(d)}, Δ^{1+o(1)}, 1 − o(1) → a constant H, the bounds C/θ₁ and e^{ε′ₙ d}, Δ^{1+εₙ} and 1 − εₙ, with εₙ, ε′ₙ → 0; reason: the meaning of the notation; both move bounds of the dense case are stated
--   - encoding: the listed point closest to q; the Δ nearest neighbors → ties broken by label; reason: ties have probability zero, and every query set is existential
--   - encoding: graphs on data points → Finset-valued maps on the labels Fin n, with IsNavGraph (no self-loop); reason: labels are identified with points in §1.2; a list has distinct entries
--   - encoding: √(log n) ≪ d ≪ log n → d/√(log n) → ∞ and d/log n → 0; reason: the meaning of ≪
--   - encoding: ρ_β, r_γ, θ₁ defined by equations in F → infima over [0, π] (capRadius); reason: F is continuous and strictly increasing for d ≥ 2
--   - encoding: the run of §1.2 → a recursion with fuel n + 1, W in ℕ∞; reason: distances strictly decrease, so the fuel is never exhausted
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 3.1, p.19

import Mathlib
import Definitions.Def_GraphNNSphere_theta1
import Definitions.Def_GraphNNSphere_rhoBeta
import Definitions.Def_GraphNNSphere_rGamma
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_IsNavGraph
import Definitions.Def_GraphNNSphere_Contains
import Definitions.Def_GraphNNSphere_maxDeg
import Definitions.Def_GraphNNSphere_greedyRun
import Definitions.Def_GraphNNSphere_W
import Definitions.Def_GraphNNSphere_thresholdGraph
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_betaStar
import Definitions.Def_GraphNNSphere_gammaC
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_IsDenseRegime

open MeasureTheory Filter Topology

namespace GraphNNSphere

open Classical in
/-- Theorem 3.1, the uniform critical degree (Lu, *Sharp Limits of Graph-Based Nearest Neighbor
Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 3.1, p.19). The
statement is a conjunction of four parts: (a) in the logarithmic regime, (a) in the dense regime,
(b) in the logarithmic regime, and (b) in the dense regime.

**Formalization Note** The quantifier order follows §2.1, p.14: the fixed parameters, then the
constants, then the sequence `d(·)`, then the vanishing sequences, then "for all large `n`", then
the query law `Q`, then the data event, then the sample, then graphs, queries and entries. So the
constants are uniform in `d(·)` and in `Q`. In (a), `Q_D` comes before `G`: one query set serves all
graphs. In (b), `E` comes before `G` and `Q_G` after it. `O(1)`, `O(1/θ₁)`, `e^{o(d)}`, `Δ^{1+o(1)}`
and `1 - o(1)` are explicit constants and vanishing sequences. A probability is the measure of an
explicit measurable set. A failing entry is one with `W = ⊤`. -/
theorem theorem_3_1 :
    -- (a), logarithmic regime
    (∀ k : ℕ, 1 ≤ k → ∀ c β β' : ℝ, 0 < c → betaStar c < β' → β' < β → β < 1 →
      ∃ η : ℝ, 0 < η ∧ ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        let Δ : ℕ := ⌈(n : ℝ) ^ β⌉₊
        ∀ Q : Measure (Sph (logDim c n)), IsProbabilityMeasure Q → Q ≪ unif (logDim c n) →
        ∃ E : Set (Fin n → Sph (logDim c n)), MeasurableSet E ∧
          1 - (n : ℝ) ^ (-η) ≤ (dataLaw n (logDim c n) E).toReal ∧
          ∀ X ∈ E, ∃ QD : Set (Sph (logDim c n)), MeasurableSet QD ∧
            1 - (n : ℝ) ^ (-η) ≤ (Q QD).toReal ∧
            ∀ q ∈ QD, ∀ G : NavGraph n,
              ((IsNavGraph G ∧ Contains G (thresholdGraph X (rhoBeta n (logDim c n) β')) ∧
                  maxDeg G ≤ 2 * Δ) ∨
                G = thresholdGraph X (rhoBeta n (logDim c n) β) ∨
                G = nnGraph X Δ) →
              ∀ x₀ : Fin n, ∃ moves expansions evals : ℕ,
                greedyRun G X q k x₀ = .success moves expansions evals ∧
                moves ≤ H ∧ (evals : ℝ) ≤ (Δ : ℝ) ^ (1 + ε n)) ∧
    -- (a), dense regime
    (∀ k : ℕ, 1 ≤ k → ∀ γ γ' : ℝ, gammaC < γ' → γ' < γ →
      ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧ ∀ d : ℕ → ℕ, IsDenseRegime d →
      ∃ ε ε' : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ Tendsto ε' atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        let Δ : ℕ := ⌈Real.exp (γ * (d n : ℝ))⌉₊
        ∀ Q : Measure (Sph (d n)), IsProbabilityMeasure Q → Q ≪ unif (d n) →
        ∃ E : Set (Fin n → Sph (d n)), MeasurableSet E ∧
          1 - Real.exp (-(c₁ * (d n : ℝ))) ≤ (dataLaw n (d n) E).toReal ∧
          ∀ X ∈ E, ∃ QD : Set (Sph (d n)), MeasurableSet QD ∧
            1 - Real.exp (-(c₂ * (d n : ℝ))) ≤ (Q QD).toReal ∧
            ∀ q ∈ QD, ∀ G : NavGraph n,
              ((IsNavGraph G ∧ Contains G (thresholdGraph X (rGamma n (d n) γ')) ∧
                  maxDeg G ≤ 2 * Δ) ∨
                G = thresholdGraph X (rGamma n (d n) γ) ∨
                G = nnGraph X Δ) →
              ∀ x₀ : Fin n, ∃ moves expansions evals : ℕ,
                greedyRun G X q k x₀ = .success moves expansions evals ∧
                (moves : ℝ) ≤ C / theta1 n (d n) ∧
                (moves : ℝ) ≤ Real.exp (ε' n * (d n : ℝ)) ∧
                (evals : ℝ) ≤ (Δ : ℝ) ^ (1 + ε n)) ∧
    -- (b), logarithmic regime
    (∀ k : ℕ, 1 ≤ k → ∀ c β : ℝ, 0 < c → 0 < β → β < betaStar c →
      ∃ a η : ℝ, 0 < a ∧ 0 < η ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        let Δ : ℕ := ⌈(n : ℝ) ^ β⌉₊
        ∃ E : Set (Fin n → Sph (logDim c n)), MeasurableSet E ∧
          1 - (n : ℝ) ^ (-η) ≤ (dataLaw n (logDim c n) E).toReal ∧
          ∀ X ∈ E, ∀ G : NavGraph n, IsNavGraph G →
            ∃ QG : Set (Sph (logDim c n)), MeasurableSet QG ∧
              1 - (n : ℝ) ^ (-η) ≤ (unif (logDim c n) QG).toReal ∧
              ∀ q ∈ QG,
                (1 - ε n) * (n : ℝ) ^ a ≤
                  ((Finset.univ.filter (fun x₀ : Fin n => (Δ : ℕ∞) ≤ W G X q k x₀)).card : ℝ) ∧
                (maxDeg G ≤ Δ → (1 - ε n) * (n : ℝ) ^ a ≤
                  ((Finset.univ.filter (fun x₀ : Fin n => W G X q k x₀ = ⊤)).card : ℝ))) ∧
    -- (b), dense regime
    (∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ, 0 < γ → γ < gammaC →
      ∃ a c₁ c₂ : ℝ, 0 < a ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∀ d : ℕ → ℕ, IsDenseRegime d →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        let Δ : ℕ := ⌈Real.exp (γ * (d n : ℝ))⌉₊
        ∃ E : Set (Fin n → Sph (d n)), MeasurableSet E ∧
          1 - Real.exp (-(c₁ * (d n : ℝ))) ≤ (dataLaw n (d n) E).toReal ∧
          ∀ X ∈ E, ∀ G : NavGraph n, IsNavGraph G →
            ∃ QG : Set (Sph (d n)), MeasurableSet QG ∧
              1 - Real.exp (-(c₂ * (d n : ℝ))) ≤ (unif (d n) QG).toReal ∧
              ∀ q ∈ QG,
                (1 - ε n) * Real.exp (a * (d n : ℝ)) ≤
                  ((Finset.univ.filter (fun x₀ : Fin n => (Δ : ℕ∞) ≤ W G X q k x₀)).card : ℝ) ∧
                (maxDeg G ≤ Δ → (1 - ε n) * Real.exp (a * (d n : ℝ)) ≤
                  ((Finset.univ.filter (fun x₀ : Fin n => W G X q k x₀ = ⊤)).card : ℝ))) := by sorry

end GraphNNSphere
