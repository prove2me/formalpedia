-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_corollary_6_31
-- name    : NonMarkovColorings.Main.corollary_6_31
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:09:40.310744+00:00
-- url     : https://prove2.me/theorems/74e06c06-c0ac-4db8-9ca6-bcc49cf9f8f8
-- title:
--   Corollary 6.31 — weighted local uniformity (6.7): $\sum_{w\in N_{\le D}(v),\,c\in A_v(X_t,w)}e^{d(w)/k}$ is within $\varepsilon\Delta$ of $|N_{\le D}(v)|$
-- statement:
--   In the setup of Theorem 6.2 (given $\delta,\varepsilon>0$ there are $C>0$ and $\Delta_0$; $G$ of maximum degree $\Delta>\Delta_0$ and girth $\ge7$, $k\ge(1+\delta)\Delta$, any start $X_0\in\widehat\Omega$, $v\in V$, $T\ge n$, $T_0\ge Cn\log\Delta$), for any color $c$, with $N_{\le D}(v)=\{w\in N(v):d(w)\le D\}$ and $A_v(X,w)=[k]\setminus X(N(w)\setminus\{v\})$,
--   $$\mathbb P\Big[\exists t\in[T_0,T_0+T],\ \exists D:\ \Big|\sum_{w\in N_{\le D}(v),\ c\in A_v(X_t,w)}e^{d(w)/k}-|N_{\le D}(v)|\Big|>\varepsilon\Delta\Big]<\frac Tn e^{-\Delta/C}.$$
--   This is property (5.3) of $\varepsilon$-uniformity, the form in which local uniformity enters the coupling analysis of §5.
--
--   Differences from the source:
--   - encoding: colors [k] = {1, …, k} → Fin k = {0, …, k−1}; reason: Lean convention; a relabeling of colors, same instances
--   - encoding: girth ≥ 7 (a forest has infinite girth) → 7 ≤ G.egirth in ℕ∞ (⊤ for a forest); reason: Mathlib's SimpleGraph.girth is 0 for forests; egirth is the girth with the forest convention
--   - encoding: probability over the discrete-time dynamics → seqProb/seqExp: normalized count/sum over update sequences σ ∈ (V × Fin k)^T, X_t = run G X0 σ t; reason: the dynamics is driven by i.i.d. uniform updates (u, c); its law up to time T is the uniform law on update sequences
--   - reading: "in the setup of Theorem 6.2" with the constant C → its own ∃ C > 0, ∃ Δ0 for given δ, ε, every X0; reason: Theorem 6.2 only asserts that some C exists and the proof enlarges C; the corollary's constants are existential in the same way
--   - encoding: D (with 0 ≤ D ≤ Δ as in (5.3)) → D : ℕ unrestricted; reason: for D ≥ Δ, N_{≤D}(v) = N(v) = N_{≤Δ}(v), so the event is unchanged
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 55, Corollary 6.31, (6.7)

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_GraphNotions
import Definitions.Def_NonMarkovColorings_Main_LabelingChain

namespace NonMarkovColorings.Main

/-- Corollary 6.31 (weighted local uniformity, (6.7)), in the setup of Theorem 6.2: for every
color `c`, with probability more than `1 − (T/n) e^{−Δ/C}`, for all `t ∈ [T0, T0 + T]` and all
`D`, `|Σ_{w ∈ N_{≤D}(v), c ∈ A_v(X_t, w)} e^{d(w)/k} − |N_{≤D}(v)|| ≤ ε Δ`. -/
theorem corollary_6_31 (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ Δ0 : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (k : ℕ), Δ0 < G.maxDegree → 7 ≤ G.egirth → (1 + δ) * (G.maxDegree : ℝ) ≤ k →
      ∀ (X0 : V → Fin k) (v : V) (T T0 : ℕ), Fintype.card V ≤ T →
        C * (Fintype.card V : ℝ) * Real.log (G.maxDegree : ℝ) ≤ T0 →
      ∀ c : Fin k,
        seqProb V k (T0 + T) (fun σ => ∃ t : ℕ, T0 ≤ t ∧ t ≤ T0 + T ∧ ∃ D : ℕ,
            |∑ w ∈ (lowDegNbrs G D v).filter (fun w => c ∈ availExcept G (run G X0 σ t) v w),
                Real.exp ((G.degree w : ℝ) / k) - ((lowDegNbrs G D v).card : ℝ)| >
              ε * (G.maxDegree : ℝ)) <
          (T : ℝ) / Fintype.card V * Real.exp (-(G.maxDegree : ℝ) / C) := by sorry

end NonMarkovColorings.Main
