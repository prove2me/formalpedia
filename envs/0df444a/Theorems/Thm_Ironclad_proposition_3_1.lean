-- Prove2me | Theorems.Thm_Ironclad_proposition_3_1
-- name    : Ironclad.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:36.927097+00:00
-- url     : https://prove2.me/theorems/70398c94-8111-44ec-b30d-a8a3723a4e08
-- title:
--   Proposition 3.1 (Markovian Property) — a semi-Markov chain with transition matrix (3) and an ergodic embedded chain
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$ and let $w$ be an i.i.d. honest characteristic string. Decompose $w$ greedily into patterns, let $X_0=S_0,X_1,X_2,\dots$ be the states of the embedded chain and $T_1,T_2,\dots$ the lengths of the successive patterns. Then:
--
--   1. **(semi-Markov chain with transition probabilities (3))** there is a kernel $K(i,j,m)$ on $\{S_0,S_1,S_2\}^2\times\mathbb N$ with $\sum_m K(i,j,m)=P_{ij}$, the matrix (3), such that for every $n$, every history $x_0,\dots,x_n$ of states and $t_1,\dots,t_n$ of lengths, and every $j,m$,
--   $$
--   \Pr(X_{0..n}=x,\ T_{1..n}=t,\ X_{n+1}=j,\ T_{n+1}=m)=\Pr(X_{0..n}=x,\ T_{1..n}=t)\cdot K(x_n,j,m);
--   $$
--   2. **(ergodic)** some power of the matrix (3) has all entries positive,
--
--   where
--   $$
--   P_{00}=P_{10}=\frac{\mathbb P(\sigma_2)+\mathbb P(\sigma_4)}{p_h},\quad P_{01}=P_{11}=\frac{\mathbb P(\sigma_1)}{p_h},\quad P_{02}=P_{12}=\frac{\mathbb P(\sigma_3)}{p_h},\quad P_{20}=\frac{\mathbb P(\sigma_4)}{q_H},\quad P_{21}=0,\quad P_{22}=\frac{\mathbb P(\sigma_3)}{q_H}.
--   $$
--
--   This is what licenses the renewal-reward arguments in the proof of Lemma 3.1.
--
--   **Formalization Note** The transition $S_0\xrightarrow{\sigma_3}$ goes to $S_2$, as in the text and in (3); the caption of Figure 3 says $S_1$, a typo.
--
--   Differences from the source:
--   - reading: $\sigma_3=\{H\}\|\{0,h\}^k$, $k\le\Delta$ (Definition 3.1) → $k<\Delta$; reason: the printed $\mathbb P(\sigma_3)$, $\mathbb P(\sigma_4)$ (p.9), on which the matrix (3) rest, hold only for $k<\Delta$
--   - reading: "is a semi-Markov chain … The transition probabilities are (3)" → existence of a Markov renewal kernel $K$ with $\sum_mK(i,j,m)=P_{ij}$ satisfying the displayed product formula for every history of states and pattern lengths; reason: the definition of a semi-Markov (Markov renewal) process with embedded transition matrix (3)
--   - reading: "its embedded Markov chain is ergodic" → some power of (3) is entrywise positive (primitive); reason: for a finite chain this is irreducible and aperiodic, the stronger of the usual readings; it holds here since $P_{00}>0$
--   - reading: no parameter range on p.10 → $0<p_h<1$, $0<q<1$, $\Delta\ge1$; reason: the proper parameters of Theorem 3.2; at $q=0$, $P_{20}$ divides by zero
--   - encoding: the decomposition starts at the first nonzero symbol from the initial state $X_0=S_0$; the i.i.d. law as hypotheses on an arbitrary probability space; slots from $0$; reason: the paper takes strings starting with $h$ or $H$ and leaves the initial state implicit; same instances
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Proposition 3.1 and Eq. (3), p.10

import Mathlib
import Definitions.Def_Ironclad_Model
import Definitions.Def_Ironclad_Decomposition
import Definitions.Def_Ironclad_ClosedForms

open MeasureTheory ProbabilityTheory Filter Topology

namespace Ironclad

/-- Proposition 3.1 (Markovian Property), Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, p.10: the
state process of the pattern decomposition is a semi-Markov chain whose embedded Markov chain is
ergodic, with transition probabilities (3).

1. (Semi-Markov chain with transition probabilities (3).) There is a kernel
   `K i j m` with `Σ_m K i j m = P_ij` (the matrix (3)) such that, for every `n`, every history of
   states `X₀, …, X_n` and pattern lengths `T₁, …, T_n`, and every `j, m`,
   `P(history, X_{n+1} = j, T_{n+1} = m) = P(history) · K(X_n, j, m)`.
2. (Ergodic.) Some power of the matrix (3) has all entries positive.

**Formalization Note** `X_k = state Δ x k` (with `X₀ = S₀`) and `T_{k+1} = patLength Δ x k`, the length
of the `k`-th pattern. "Ergodic" is read as primitive (some power positive), which for a finite
chain is irreducible and aperiodic. The i.i.d. honest string is
`IsHonestString μ w ph q` on an arbitrary probability space; slots are indexed from `0`; the
standing parameter range `0 < p_h, q < 1`, `Δ ≥ 1` is that of Theorem 3.2. -/
theorem proposition_3_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : ℕ → Ω → Sym) (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) (hw : IsHonestString μ w ph q) :
    (∃ K : Fin 3 → Fin 3 → ℕ → ℝ, (∀ i j, HasSum (K i j) (Pmat ph q Δ i j)) ∧
      ∀ (n : ℕ) (xs : Fin (n + 1) → Fin 3) (ts : Fin n → ℕ) (j : Fin 3) (m : ℕ),
        μ.real {ω | (∀ k : Fin (n + 1), state Δ (fun t => w t ω) k = xs k) ∧
            (∀ k : Fin n, patLength Δ (fun t => w t ω) k = some (ts k)) ∧
            state Δ (fun t => w t ω) (n + 1) = j ∧ patLength Δ (fun t => w t ω) n = some m} =
          μ.real {ω | (∀ k : Fin (n + 1), state Δ (fun t => w t ω) k = xs k) ∧
            (∀ k : Fin n, patLength Δ (fun t => w t ω) k = some (ts k))} *
            K (xs (Fin.last n)) j m) ∧
    ∃ N : ℕ, ∀ i j, 0 < (Pmat ph q Δ ^ N) i j := by sorry

end Ironclad
