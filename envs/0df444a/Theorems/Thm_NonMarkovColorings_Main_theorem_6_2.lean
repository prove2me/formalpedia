-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_theorem_6_2
-- name    : NonMarkovColorings.Main.theorem_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:10:34.068477+00:00
-- url     : https://prove2.me/theorems/c35e545d-00ef-4e54-80a1-6a1daff0f93f
-- title:
--   Theorem 6.2 — local uniformity of the discrete-time Metropolis dynamics after $Cn\log\Delta$ steps: available colors, blocked subsets, color counts
-- statement:
--   Given $\delta,\varepsilon>0$ there are $C=C(\delta,\varepsilon)>0$ and $\Delta_0=\Delta_0(\delta,\varepsilon)$ such that the following holds. Let $G=(V,E)$ be a graph with $n=|V|$ vertices, maximum degree $\Delta>\Delta_0$ and girth at least $7$, and let $k\ge(1+\delta)\Delta$. Let $(X_t)_{t\ge0}$ be the discrete-time Metropolis dynamics on all labelings $\widehat\Omega=[k]^V$ from any $X_0$. Fix $v\in V$, an interval length $T\ge n$ and a start time $T_0\ge Cn\log\Delta$. Then
--   $$\mathbb P\big[\exists t\in[T_0,T_0+T]:\ \big||A(X_t,v)|-ke^{-d(v)/k}\big|>\varepsilon k\big]\le \tfrac Tn e^{-\Delta/C};$$
--   for any $S\subseteq N(v)$, colors $c_1\ne c_2$ and $i_1,i_2\in\mathbb N$,
--   $$\mathbb P\Big[\exists t:\ \Big||S_{c_1,i_1}(X_t)\cap S_{c_2,i_2}(X_t)|-\sum_{w\in S}\frac{e^{-2d(w)/k}}{i_1!\,i_2!}\Big(\frac{d(w)}k\Big)^{i_1+i_2}\Big|>\varepsilon\Delta\Big]\le\tfrac Tn e^{-\Delta/C};$$
--   and for any color $c$, $\mathbb P[\exists t: |X_t^{-1}(c)\cap B_2(v)|>399\Delta \text{ or } |X_t^{-1}(c)\cap N(v)|>399\Delta/\log\Delta]\le\frac Tn\exp(-\Delta/C)$, with $t$ ranging over $[T_0,T_0+T]$ in each event. This is the Metropolis analogue of Hayes' local uniformity; it contains Theorem 1.4 (the first bound) and supplies the "burn-in" of the contraction argument.
--
--   **Formalization Note.** The probability is over $\vec\sigma$ uniform in $(V\times[k])^{T_0+T}$ (`seqProb`), $X_t=$ `run G X0 σ t`; $T,T_0\in\mathbb N$.
--
--   Differences from the source:
--   - encoding: colors [k] = {1, …, k} → Fin k = {0, …, k−1}; reason: Lean convention; a relabeling of colors, same instances
--   - encoding: girth ≥ 7 (a forest has infinite girth) → 7 ≤ G.egirth in ℕ∞ (⊤ for a forest); reason: Mathlib's SimpleGraph.girth is 0 for forests; egirth is the girth with the forest convention
--   - encoding: probability over the discrete-time dynamics → seqProb/seqExp: normalized count/sum over update sequences σ ∈ (V × Fin k)^T, X_t = run G X0 σ t; reason: the dynamics is driven by i.i.d. uniform updates (u, c); its law up to time T is the uniform law on update sequences
--   - reading: the dynamics on Ω̂ (start state not named) → ∀ X0 : V → Fin k; reason: the strongest reading; the proof works from an arbitrary initial labeling
--   - reading: constant C = C(δ, ε) → 0 < C; reason: C > 0 is implicit in e^{−Δ/C} and T0 ≥ Cn log Δ; C ≤ 0 would make the bounds degenerate
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 41, Theorem 6.2

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_GraphNotions
import Definitions.Def_NonMarkovColorings_Main_LabelingChain
import Definitions.Def_NonMarkovColorings_Main_LocalUniformity

namespace NonMarkovColorings.Main

/-- Theorem 6.2 (local uniformity of the discrete-time Metropolis dynamics on all labelings).
For `δ, ε > 0` there are `C > 0` and `Δ0` such that for every graph of maximum degree `Δ > Δ0`
and girth `≥ 7`, every `k ≥ (1 + δ)Δ`, every start `X0`, vertex `v`, window length `T ≥ n` and
start time `T0 ≥ C n log Δ`, each of the three events "for some `t ∈ [T0, T0 + T]` …" has
probability at most `(T/n) e^{−Δ/C}` over uniform update sequences of length `T0 + T`. -/
theorem theorem_6_2 (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ Δ0 : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (k : ℕ), Δ0 < G.maxDegree → 7 ≤ G.egirth → (1 + δ) * (G.maxDegree : ℝ) ≤ k →
      ∀ (X0 : V → Fin k) (v : V) (T T0 : ℕ), Fintype.card V ≤ T →
        C * (Fintype.card V : ℝ) * Real.log (G.maxDegree : ℝ) ≤ T0 →
      seqProb V k (T0 + T) (fun σ => ∃ t : ℕ, T0 ≤ t ∧ t ≤ T0 + T ∧
          |((avail G (run G X0 σ t) v).card : ℝ) - k * Real.exp (-((G.degree v : ℝ) / k))| >
            ε * k) ≤
        (T : ℝ) / Fintype.card V * Real.exp (-(G.maxDegree : ℝ) / C) ∧
      (∀ S : Finset V, S ⊆ G.neighborFinset v → ∀ c1 c2 : Fin k, c1 ≠ c2 → ∀ i1 i2 : ℕ,
        seqProb V k (T0 + T) (fun σ => ∃ t : ℕ, T0 ≤ t ∧ t ≤ T0 + T ∧
            |((blockedSubset G (run G X0 σ t) v S c1 i1 ∩
                blockedSubset G (run G X0 σ t) v S c2 i2).card : ℝ) -
              ∑ w ∈ S, Real.exp (-(2 * (G.degree w : ℝ)) / k) /
                ((i1.factorial : ℝ) * (i2.factorial : ℝ)) * ((G.degree w : ℝ) / k) ^ (i1 + i2)| >
              ε * (G.maxDegree : ℝ)) ≤
          (T : ℝ) / Fintype.card V * Real.exp (-(G.maxDegree : ℝ) / C)) ∧
      (∀ c : Fin k,
        seqProb V k (T0 + T) (fun σ => ∃ t : ℕ, T0 ≤ t ∧ t ≤ T0 + T ∧
            ((((ball G 2 {v}).filter fun u => run G X0 σ t u = c).card : ℝ) >
                399 * (G.maxDegree : ℝ) ∨
              (((G.neighborFinset v).filter fun u => run G X0 σ t u = c).card : ℝ) >
                399 * (G.maxDegree : ℝ) / Real.log (G.maxDegree : ℝ))) ≤
          (T : ℝ) / Fintype.card V * Real.exp (-(G.maxDegree : ℝ) / C)) := by sorry

end NonMarkovColorings.Main
