-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_lemma_1
-- name    : OfflineCMC.Minimax.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:05.974282+00:00
-- url     : https://prove2.me/theorems/858c0749-7750-46b6-9a83-7c842dd129ff
-- title:
--   Lemma 1 (corrected: φ_{i,j} ≤ Σ_{r≤i} η̄_{r,j}; φ ≤ η̄ is false) — η̄_{i,j} ≤ 2φ_{i,j} and the telescoped bound on φ_{i,j}
-- statement:
--   Let $\{(X_i,a_i)\}$ be a controlled Markov chain. Let $\bar\eta_{i,j}$ and $\phi_{i,j}$ be the weak and uniform mixing coefficients of eqs. (2.1)–(2.2) on the window up to time $m$. Then for all $0\le i<j\le m$,
--   $$
--   \bar\eta_{i,j}\le 2\phi_{i,j}\qquad\text{and}\qquad \phi_{i,j}\le\sum_{r=0}^{i}\bar\eta_{r,j}.
--   $$
--
--   The two inequalities compare the weak and the uniform mixing coefficient. The second one turns the exponential decay of $\bar\eta$ (Assumption 4, for all $r\ge0$) into the decay $\phi_{i,j}\le C_\Delta((C_\Delta-1)/C_\Delta)^{j-i}$ of the uniform coefficient. That decay is what the covariance bound (Lemma 9) and the Bernstein inequality behind Proposition 3 use.
--
--   **Formalization Note** The window $((X_j,a_j),\dots,(X_m,a_m))$ is listed in increasing time order. Events are arbitrary subsets of its finite range, and the suprema are finite maxima, $0$ when no index is admissible.
--
--   Differences from the source:
--   - correction: $\phi_{i,j}\le\bar\eta_{i,j}$ → $\phi_{i,j}\le\sum_{r=0}^{i}\bar\eta_{r,j}$; reason: the printed inequality is false. Take two controls, $M^{(1)}=M^{(2)}$ with all entries $1/2$ on two states, $a_0$ uniform and $a_i=a_{i-1}$ for $i\ge1$. For $i\ge1$ the history fixes $a_i$, $X_i$ takes both values and the future does not depend on it, so $\bar\eta_{i,j}=0$. But $\mathbb P(a_j=1)=1/2$ while $\mathbb P(a_j=1\mid\mathcal H^i_0)\in\{0,1\}$, so $\phi_{i,j}=1/2$.
--   - reading: "$i<j\le m$" → $0\le i<j\le m$, with the empty history at $i=0$; reason: eq. (2.1) takes $\hbar^{i-1}_0\in(\chi\times\mathbb I)^i$, which is the empty sequence at $i=0$
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 8, Lemma 1; eqs. (2.1)–(2.2), p. 8

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC
import Definitions.Def_OfflineCMC_Minimax_Model

namespace OfflineCMC.Minimax

open MeasureTheory

theorem lemma_1 {d k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (C : CMC d k μ) (m i j : ℕ) (hij : i < j) (hjm : j ≤ m) :
    C.etaBar m i j ≤ 2 * C.phi m i j ∧
      C.phi m i j ≤ ∑ r ∈ Finset.range (i + 1), C.etaBar m r j := by sorry

end OfflineCMC.Minimax
