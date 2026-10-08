-- Prove2me | Theorems.Thm_FriezeKannan_PseudoReg_lemma_7a
-- name    : FriezeKannan.PseudoReg.lemma_7a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:15.438623+00:00
-- url     : https://prove2.me/theorems/d11230d2-afe6-44d6-a4c3-26efeae3b6ae
-- title:
--   Lemma 7(a), p. 203 — if Q refines P and M is compatible with P, then sup|A(S,T) − A_Q(S,T)| ≤ 2 sup|A(S,T) − M(S,T)|
-- statement:
--   Let $V$ be a finite set, $\mathbf A$ and $\mathbf M$ real $V\times V$ matrices, $\mathcal P$ a partition of $V$, and $\mathcal Q=W_1,\dots,W_\ell$ a refinement of $\mathcal P$. If $\mathbf M$ is compatible with $\mathcal P$, then
--   $$\sup_{S,T\subseteq V}|\mathbf A(S,T)-\mathbf A_{\mathcal Q}(S,T)|\le 2\sup_{S,T\subseteq V}|\mathbf A(S,T)-\mathbf M(S,T)|.$$
--   Here $\mathbf A_{\mathcal Q}$ is the block average of $\mathbf A$ over the blocks $W_i\times W_j$, and both suprema range over all pairs of subsets of $V$ (a finite family, so they are maxima).
--
--   The lemma says that, up to a factor 2 in the cut norm, block-averaging $\mathbf A$ over any refinement of $\mathcal P$ approximates $\mathbf A$ as well as the best matrix that is constant on the blocks of $\mathcal P$.
--
--   **Formalization Note.** The inequality between suprema is stated in the equivalent form: for every real $c$, if $|\mathbf A(S,T)-\mathbf M(S,T)|\le c$ for all $S,T\subseteq V$, then $|\mathbf A(S,T)-\mathbf A_{\mathcal Q}(S,T)|\le 2c$ for all $S,T\subseteq V$. In Section 5.1 $\mathbf A$ is an adjacency matrix; the lemma uses nothing about it and is stated for every real matrix $\mathbf A$. "$\mathcal Q$ refines $\mathcal P$" is Mathlib's order on `Finpartition` ($\mathcal Q\le\mathcal P$: every part of $\mathcal Q$ lies in a part of $\mathcal P$).
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 203, Lemma 7(a)

import Mathlib
import Definitions.Def_FriezeKannan_PseudoReg_Setting

namespace FriezeKannan.PseudoReg

theorem lemma_7a {V : Type*} [Fintype V] [DecidableEq V]
    (A M : Matrix V V ℝ) (P Q : Finpartition (Finset.univ : Finset V)) (hQP : Q ≤ P)
    (hM : Compatible P M) (c : ℝ)
    (hc : ∀ S T : Finset V, |blockSum (A - M) S T| ≤ c) :
    ∀ S T : Finset V, |blockSum (A - blockAvg Q A) S T| ≤ 2 * c := by sorry

end FriezeKannan.PseudoReg
