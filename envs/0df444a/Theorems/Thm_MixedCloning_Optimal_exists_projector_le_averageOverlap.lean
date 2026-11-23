-- Prove2me | Theorems.Thm_MixedCloning_Optimal_exists_projector_le_averageOverlap
-- name    : MixedCloning.Optimal.exists_projector_le_averageOverlap
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:03:32.788502+00:00
-- url     : https://prove2.me/theorems/2f24edb5-f645-4f77-aaea-56faf95482b7
-- title:
--   Lemma 14 averaging step — a rotated projector below the Haar-average overlap
-- statement:
--   Let $C$ be a channel from $n$ copies in dimension $d$ to $m$ copies, and fix $0\le r\le d$. There is a rank-$r$ orthogonal projector $P$, of the form $UP_0U^\dagger$ for a unitary $U$ and the standard last-coordinate projector $P_0$, such that
--
--   $$
--   \operatorname{tr}\!\left(C((P/r)^{\otimes n})P^{\otimes m}\right)
--   \le \int_{U(d)}\operatorname{tr}\!\left(C(((UP_0U^\dagger)/r)^{\otimes n})(UP_0U^\dagger)^{\otimes m}\right)\,dU.
--   $$
--
--   The witness is obtained at a unitary whose overlap is at most the normalized Haar average. This is the worst-case-to-average-case reduction at the start of the proof of Lemma 14, including arbitrary $n,m\ge0$; no positivity of $r$ is needed because the projector-state scalar is used only through its definition.
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 18, proof of Lemma 14, Eq. (6), first inequality (minimum is at most the Haar average)

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

theorem MixedCloning.Optimal.exists_projector_le_averageOverlap (d r n m : ℕ) (hrd : r ≤ d)
    (C : MixedCloning.Optimal.Cloner d n m) (hC : QAlgorithms.IsChannel C) :
    ∃ P : MixedCloning.Optimal.Op (Fin d), MixedCloning.Optimal.IsProjector r P ∧
      MixedCloning.Optimal.overlap d r n m C P ≤ MixedCloning.Optimal.averageOverlap d r n m C := by sorry
