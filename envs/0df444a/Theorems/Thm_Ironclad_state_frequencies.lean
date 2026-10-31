-- Prove2me | Theorems.Thm_Ironclad_state_frequencies
-- name    : Ironclad.state_frequencies
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:23.538946+00:00
-- url     : https://prove2.me/theorems/5e6b1cac-14f5-4437-97e3-4c9554ae6be3
-- title:
--   Appendix .2.3, pp.30–31 — $\#_LS_i/L\to\pi_i/\sum_j\pi_j\mu_j$ almost surely
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$ and let $w$ be an i.i.d. honest characteristic string. Let $\#_LS_i$ be the number of sojourns in state $S_i$ within the first $L$ slots, $\pi$ the stationary distribution of App. .2.2 and $\mu_j=\sum_kP_{jk}l_{jk}$ the expected sojourn times. Then almost surely, for every state $i$,
--
--   $$
--   \frac{\#_LS_i}{L}\xrightarrow[L\to\infty]{}\frac1{\mu_{ii}}=\frac{\pi_i}{\sum_{j=0}^2\pi_j\mu_j},
--   $$
--
--   where $\mu_{ii}$ is the expected time between two consecutive visits of $S_i$. The first limit is the renewal theorem the paper applies on p.30, and the identity $1/\mu_{ii}=\pi_i/\sum_j\pi_j\mu_j$ is the theorem of its reference [29] quoted on p.31.
--
--   These per-slot visit rates are the first factor in each term of $\alpha$.
--
--   **Formalization Note** A sojourn is counted in the period of length $L$ when its pattern lies in the slots $0,\dots,L-1$.
--
--   Differences from the source:
--   - reading: $\sigma_3=\{H\}\|\{0,h\}^k$, $k\le\Delta$ (Definition 3.1) → $k<\Delta$; reason: the printed $\mathbb P(\sigma_3)$, $\mathbb P(\sigma_4)$ (p.9), on which the matrix (3) and the limits rest, hold only for $k<\Delta$
--   - reading: $\#_LS_i/L\to1/\mu_{ii}$ (p.30) and $1/\mu_{ii}=\pi_i/\sum_j\pi_j\mu_j$ ([29], p.31) → the combined limit $\pi_i/\sum_j\pi_j\mu_j$; reason: the paper uses the two together; $\mu_{ii}$ is not defined by a formula in the paper
--   - generalization: the limit for $S_0$ (and $S_1$, p.31) → for all three states, almost surely simultaneously; reason: specializes to $i=0,1$
--   - reading: no parameter range in App. .2.3 → $0<p_h<1$, $0<q<1$, $\Delta\ge1$; reason: the proper parameters of Theorem 3.2
--   - encoding: the counting window of $\#_L$ (patterns lying in slots $0,\dots,L-1$); decomposition from the first nonzero symbol with $X_0=S_0$; the i.i.d. law as hypotheses on an arbitrary probability space; reason: the paper does not fix a window or initial state; boundary effects change counts by $O(1)$ and do not affect the limit
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Appendix .2.3, proof of Lemma 3.1, p.30 ("#LS0/L → 1/µ00") and p.31 ("The theorem in [29] shows")

import Mathlib
import Definitions.Def_Ironclad_Model
import Definitions.Def_Ironclad_Decomposition
import Definitions.Def_Ironclad_ClosedForms

open MeasureTheory ProbabilityTheory Filter Topology

namespace Ironclad

/-- The visit frequencies of the states per time slot, Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, Appendix .2.3, pp.30–31: almost surely `#_L S_i / L → 1/μ_ii = π_i / Σ_j π_j μ_j`, where `μ_ii` is the
mean time between consecutive visits of `S_i` ("the renewal theorem yields `#_L S₀/L → 1/μ₀₀`",
p.30) and the identity `1/μ_ii = π_i/Σ_j π_j μ_j` is the theorem of [29] quoted on p.31.

**Formalization Note** `#_L S_i` is `cntState`, the number of sojourns in `S_i` whose pattern lies
in the slots `0, …, L − 1`. The limit is written with [29]'s identity substituted for `1/μ_ii`.
The paper uses `i = 0, 1`; the statement covers all three states. The i.i.d. honest string is
`IsHonestString μ w ph q` on an arbitrary probability space; slots are indexed from `0`; the
standing parameter range `0 < p_h, q < 1`, `Δ ≥ 1` is that of Theorem 3.2. -/
theorem state_frequencies {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : ℕ → Ω → Sym) (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) (hw : IsHonestString μ w ph q) :
    ∀ᵐ ω ∂μ, ∀ i : Fin 3,
      Tendsto (fun L : ℕ => (cntState Δ (fun t => w t ω) L i : ℝ) / L) atTop
        (𝓝 (piStat ph q Δ i / meanCycle ph q Δ)) := by sorry

end Ironclad
