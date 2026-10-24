-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_proposition_1
-- name    : OfflineCMC.Minimax.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:11.477764+00:00
-- url     : https://prove2.me/theorems/ab45211c-982b-43b0-b156-55243411e308
-- title:
--   Proposition 1 (corrected: √(d/n_low) in place of √(d/n_high)) — row error of the empirical estimator at bounded visit counts
-- statement:
--   Let $\{(X_i,a_i)\}$ be a controlled Markov chain with $d$ states and transition matrices $M^{(l)}$. Let $\hat M^{(l)}$ be the empirical estimator of eq. (1.2) built from the counts $N^{(l)}_s$, $N^{(l)}_{s,t}$ of eq. (1.1) over the times $1,\dots,m$. Fix a state $s$, a control $l$, a number $\varepsilon$ and integers $0<n_{low}<n_{high}<m$. Then
--   $$
--   \mathbb P\Big(\big\|\hat M^{(l)}(s,\cdot)-M^{(l)}(s,\cdot)\big\|_1>\varepsilon,\ n_{low}\le N^{(l)}_s\le n_{high}\Big)\le m\exp\Big(-\frac{n_{low}}{2}\max\Big\{0,\varepsilon-\sqrt{d/n_{low}}\Big\}^2\Big).
--   $$
--
--   No mixing or return-time assumption is needed. The bound controls the estimator's row error on the event that the visit count lies in a prescribed window. In the proof of Theorem 2 it is applied with $n_{low}=m/(4T)$.
--
--   **Formalization Note** The row distance is the $\ell^1$ distance between the $s$-th rows. On the event, $N^{(l)}_s\ge n_{low}\ge1$, so the convention $0/0=0$ of the estimator never enters.
--
--   Differences from the source:
--   - correction: $\max\{0,\varepsilon-\sqrt{d/n_{high}}\}$ → $\max\{0,\varepsilon-\sqrt{d/n_{low}}\}$; reason: as printed the bound is false: one control, $X_i$ i.i.d. uniform on $d=1000$ states, $\varepsilon=1$, $m=10^5$, $n_{low}=50$, $n_{high}=99999$. Then $N_s\sim\mathrm{Bin}(10^5,10^{-3})$ lies in $[50,200]$ with probability close to $1$, and there the row error is at least $2(1-200/1000)=1.6>\varepsilon$. The printed right side is $10^5e^{-25(1-\sqrt{1000/99999})^2}\approx1.6\cdot10^{-4}$. The map $n\mapsto n\max(0,\varepsilon-\sqrt{d/n})^2$ is increasing, so its minimum over $[n_{low},n_{high}]$ is at $n_{low}$.
--   - reading: the sample is $(X_0,a_0),\dots,(X_m,a_m)$ → the counts of eq. (1.1) over $i=1,\dots,m$, which read $X_{m+1}$; reason: eq. (1.1) defines $N^{(l)}_{s,t}$ with $X_{i+1}$ for $i\le m$, and keeping both counts on the same index set makes every nonempty row of $\hat M^{(l)}$ a probability vector
--   - encoding: $\hat M^{(l)}_{s,t}=N^{(l)}_{s,t}/N^{(l)}_s$ → Lean division with $0/0=0$; reason: the event requires $N^{(l)}_s\ge n_{low}\ge1$, so no instance changes
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 9, Proposition 1, eq. (3.2)

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC
import Definitions.Def_OfflineCMC_Minimax_Model

namespace OfflineCMC.Minimax

open MeasureTheory

theorem proposition_1 {d k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (C : CMC d k μ) (m : ℕ) (l : Fin k) (s : Fin d) (ε : ℝ)
    (nlow nhigh : ℕ) (hlow : 0 < nlow) (hlh : nlow < nhigh) (hhm : nhigh < m) :
    μ.real {ω | ε < rowDist (fun s' t => C.Mhat m l s' t ω) (C.M l) s ∧
        nlow ≤ C.count m l s ω ∧ C.count m l s ω ≤ nhigh} ≤
      (m : ℝ) * Real.exp (-((nlow : ℝ) / 2) *
        (max 0 (ε - Real.sqrt ((d : ℝ) / (nlow : ℝ)))) ^ 2) := by sorry

end OfflineCMC.Minimax
