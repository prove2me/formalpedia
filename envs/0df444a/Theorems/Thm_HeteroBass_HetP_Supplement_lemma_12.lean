-- Prove2me | Theorems.Thm_HeteroBass_HetP_Supplement_lemma_12
-- name    : HeteroBass.HetP.Supplement.lemma_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:30:34.258+00:00
-- url     : https://prove2.me/theorems/c0286963-4902-4e54-9438-551a59c2a717
-- title:
--   Lemma 12 (corrected: anchored extension and coincident neighbor) — complete circle IVP
-- statement:
--   Consider the heterogeneous two-sided Bass circle of any finite size $M\ge2$, with nonnegative external and directed neighbor rates and positive total incoming influence at every node. There is no mild-heterogeneity restriction. Define $[S^j_{m,n}](t)$ as the generator-process nonadoption probability on $U^j_{m,n}=\{j-m,\ldots,j+n\}$, with indices modulo $M$. For every $j$ and every $m,n\ge0$ with $m+n\le M-2$, these probabilities satisfy
--
--   $$\begin{aligned}
--   \frac{d}{dt}[S^j_{m,n}]&=-\left(\sum_{i\in U^j_{m,n}}p_i+L+R\right)[S^j_{m,n}]
--   +R[S^j_{m,n+1}]+L[S^j_{m+1,n}],\\
--   L&=Q_{j-m-1,j-m},\qquad R=Q_{j+n+1,j+n},\quad (M\ge3).
--   \end{aligned}$$
--
--   For $M=2$, replace $R$ by zero to count the unique peer edge once. For all sizes, the complete system also contains
--
--   $$[S_M]'=-\left(\sum_i p_i\right)[S_M],\qquad [S^j_{m,n}](0)=1\quad(m+n+1\le M),$$
--
--   and every full interval $m+n+1=M$ equals the single all-node probability $[S_M](t)$ for every $t\ge0$.
--
--   This is the complete initial-value system used to determine the singleton probabilities in Theorem 7. It concerns observations of the existing chain, rather than an independently defined candidate ODE solution. Repeated eigenvalues and vanishing individual external rates are included.
--
--   Differences from the source:
--   - correction: (46a) prints the left extension as [S_{m+1,n}] without j → the left extension keeps the same anchor j; reason: Appendix K, p. 34 identifies the enlarged interval as {j−m−1,…,j+n}; the missing superscript is a notation error and no case is excluded
--   - correction: literal substitution M=2 in the two-boundary notation repeats the same directed edge → the M=2 singleton equation uses its unique peer weight once; reason: p. 19 defines one-sided and two-sided two-node circles to be identical, consistently with (23), p. 8; at p_1=p_2=Q_{1,2}=Q_{2,1}=1 the correct singleton is (1+t)e^(−2t), which fails the duplicated-edge equation for t>0; no network size is excluded
--   - encoding: all anchored interval equations, full-interval identifications and initial data in physical time → SolvesCircleIVP for the generator observations, a shared full coordinate, explicit full-interval equality and initial values, with derivatives on [0,∞); reason: the finite coordinates include every proper interval for every anchor and identify every length-M interval; explicit nonnegative rates and positive incoming totals express (4)–(7)
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, Lemma 12, (46a)–(46c), pp. 18–19; Appendix K, p. 34; (23), p. 8

import Mathlib
import Definitions.Def_HeteroBass_HetP_Supplement_IntervalIVP

namespace HeteroBass.HetP.Supplement

theorem lemma_12 {M : ℕ} (hM : 2 ≤ M) (p : Fin M → ℝ)
    (Q : Fin M → Fin M → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hQ : ∀ k j, k ≠ j → 0 ≤ Q k j)
    (hin : ∀ j, 0 < ∑ k ∈ Finset.univ.erase j, Q k j)
    (hcircle : IsTwoSidedCircle Q) :
    SolvesCircleIVP p Q (circleObservation p Q) ∧
    (∀ j : Fin M, ∀ m n : ℕ, m + n + 1 = M → ∀ t : ℝ, 0 ≤ t →
      intervalNonadoption p Q j m n t = subsetNonadoption p Q Finset.univ t) ∧
    (∀ j : Fin M, ∀ m n : ℕ, m + n + 1 ≤ M →
      intervalNonadoption p Q j m n 0 = 1) := by sorry

end HeteroBass.HetP.Supplement
