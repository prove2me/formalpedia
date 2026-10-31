-- Prove2me | Theorems.Thm_Ironclad_edge_lengths
-- name    : Ironclad.edge_lengths
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:33.589141+00:00
-- url     : https://prove2.me/theorems/dbd6b0c5-5c8a-4fb6-959d-312e0303f6b0
-- title:
--   Appendix .2.1 — expected edge lengths $l_{ij}$
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$, let $w$ be an i.i.d. honest characteristic string, and let $X_n$ and $T_{n+1}$ be the state before and the length of the $n$-th pattern. For every $n$ and all states $i,j$, the length $T_{n+1}$ is integrable on the event $\{X_n=i,\ X_{n+1}=j\}$ and
--
--   $$
--   \mathbb E\big[T_{n+1};\ X_n=i,\ X_{n+1}=j\big]=\Pr(X_n=i)\,P_{ij}\,l_{ij},
--   $$
--
--   where $P$ is the matrix (3) and
--
--   $$
--   l_{00}=l_{10}=\frac{\mathbb P(\sigma_2)\mathbb E|\sigma_2|+\mathbb P(\sigma_4)\mathbb E|\sigma_4|}{\mathbb P(\sigma_2)+\mathbb P(\sigma_4)},\quad l_{01}=l_{11}=\mathbb E|\sigma_1|,\quad l_{02}=l_{12}=l_{22}=\mathbb E|\sigma_3|,\quad l_{20}=\mathbb E|\sigma_4|,\quad l_{21}=0.
--   $$
--
--   That is, $l_{ij}$ is the expected length of a transition from $S_i$ to $S_j$; the sojourn times $\mu_i=\sum_jP_{ij}l_{ij}$ of Lemma 3.1 are built from them.
--
--   **Formalization Note** $T_{n+1}$ is read as $0$ on the null event that the decomposition stops before the $n$-th pattern.
--
--   Differences from the source:
--   - reading: $\sigma_3=\{H\}\|\{0,h\}^k$, $k\le\Delta$ (Definition 3.1) → $k<\Delta$; reason: the printed $\mathbb P(\sigma_3)$, $\mathbb P(\sigma_4)$ (p.9), on which the matrix (3) and the lengths l_ij rest, hold only for $k<\Delta$
--   - reading: "the expressions for expected edge length $l_{ij}$" → $\mathbb E[T_{n+1};X_n=i,X_{n+1}=j]=\Pr(X_n=i)P_{ij}l_{ij}$ for every $n$, with integrability; reason: $l_{ij}$ is the conditional mean length of an $S_i\to S_j$ transition; the product form avoids dividing by $\Pr(X_n=i)$ (zero for $i\neq0$, $n=0$) and by $P_{21}=0$
--   - reading: no parameter range in App. .2.1 → $0<p_h<1$, $0<q<1$, $\Delta\ge1$; reason: the proper parameters of Theorem 3.2
--   - encoding: decomposition from the first nonzero symbol with $X_0=S_0$; $T_{n+1}$ read as $0$ once the decomposition has stopped (a null event); the i.i.d. law as hypotheses on an arbitrary probability space; slots from $0$; reason: same instances
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Appendix .2.1, p.30, with E|σ_i| from p.9

import Mathlib
import Definitions.Def_Ironclad_Model
import Definitions.Def_Ironclad_Decomposition
import Definitions.Def_Ironclad_ClosedForms

open MeasureTheory ProbabilityTheory Filter Topology

namespace Ironclad

/-- The expected edge lengths, Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, Appendix .2.1, p.30:
`l_ij` is the expected length of a transition `S_i → S_j`, i.e. for every step `n`,
`E[T_{n+1} ; X_n = i, X_{n+1} = j] = P(X_n = i) · P_ij · l_ij`.

**Formalization Note** `X_k = state Δ x k` and `T_{n+1}` is `patLength Δ x n` (read as `0` when the
decomposition has stopped, a null event). The i.i.d. honest string is
`IsHonestString μ w ph q` on an arbitrary probability space; slots are indexed from `0`; the
standing parameter range `0 < p_h, q < 1`, `Δ ≥ 1` is that of Theorem 3.2. -/
theorem edge_lengths {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : ℕ → Ω → Sym) (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) (hw : IsHonestString μ w ph q) (n : ℕ) (i j : Fin 3) :
    IntegrableOn (fun ω => ((patLength Δ (fun t => w t ω) n).getD 0 : ℝ))
      {ω | state Δ (fun t => w t ω) n = i ∧ state Δ (fun t => w t ω) (n + 1) = j} μ ∧
    ∫ ω in {ω | state Δ (fun t => w t ω) n = i ∧ state Δ (fun t => w t ω) (n + 1) = j},
        ((patLength Δ (fun t => w t ω) n).getD 0 : ℝ) ∂μ =
      μ.real {ω | state Δ (fun t => w t ω) n = i} *
        (Pmat ph q Δ i j * lmat ph q Δ i j) := by sorry

end Ironclad
