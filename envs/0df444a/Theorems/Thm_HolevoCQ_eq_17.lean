-- Prove2me | Theorems.Thm_HolevoCQ_eq_17
-- name    : HolevoCQ.eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:15.4267+00:00
-- url     : https://prove2.me/theorems/b9972634-8af4-44ba-a33f-2348a67c9e84
-- title:
--   Eq. (17): the error bound $P_{er}\le\frac1N\sum_u\{3\mathrm{Tr}S_u(I-P)+\dots\}$
-- statement:
--   Let $S_{u_1},\dots,S_{u_N}$ ($N\ge1$) be density operators, let $P$ be an orthogonal projector and let $P_{u_k}$ be orthogonal projectors with $P_{u_k}$ commuting with $S_{u_k}$. Decode with the operators (11), $X_u=G^{-1/2}PP_uPG^{-1/2}$, $G=\sum_{u'}PP_{u'}P$. Then the average error probability satisfies
--
--   $$
--   P_{er}\le\frac1N\sum_{u=1}^N\Big\{3\,\mathrm{Tr}\,S_u(I-P)+\sum_{u':u'\ne u}\mathrm{Tr}\,PS_uPP_{u'}+\mathrm{Tr}\,S_u(I-P_u)\Big\}.
--   $$
--
--   Here $u,u'$ run over the code positions $1,\dots,N$, so coinciding words are allowed. This is the one-shot error estimate on which the random-coding argument of §6 rests.
--
--   Differences from the source:
--   - generalization: $P$ the typical projector (6), $P_u$ the typical projector (8) of the word state $S_u$ → any orthogonal projector $P$; any orthogonal projectors $Q_k$ commuting with density operators $T_k$ on any finite-dimensional space; reason: the derivation on pp.4–6 uses only that $P$ is an orthogonal projector and that $P_u$ is a sum of eigenprojectors of $S_u$ (equivalently, a projector commuting with $S_u$); the paper's $P$, $P_u$, $S_u$ satisfy these hypotheses
--   - encoding: a code of size $N$ (implicitly $N\ge1$) → hypothesis `1 ≤ N`; reason: $1/N$ is undefined at $N=0$; the hypothesis excludes only that case
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are real
--   - encoding: the generalized inverse $X^{-1/2}$ of $X^{1/2}$ in (11) → `genInvSqrt`, `cfc` of $x\mapsto(\sqrt x)^{-1}$ with $(\sqrt0)^{-1}=0$ (inside `sqrtMeas`); reason: equal to $0$ on the kernel and $(X^{1/2})^{-1}$ on its orthogonal complement, the paper's definition
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (17), p.6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_avgError
import Definitions.Def_HolevoCQ_sqrtMeas

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (17), p.6: for the decision rule (11),
`P_er ≤ (1/N) Σ_{u=1}^N {3 Tr S_u(I − P) + Σ_{u' ≠ u} Tr P S_u P P_{u'} + Tr S_u(I − P_u)}`.

**Formalization Note.** Code positions are `k : Fin N` (words may repeat); `T k` is the density
operator `S_{u_k}`. Stated for every orthogonal projector `P` and every orthogonal projector
`Q k` commuting with `T k` (the paper's `P` is (6) and its `P_{u_k}` (8), a sum of
eigenprojectors of `S_{u_k}`; the derivation on pp.4–6 uses only these properties). Traces are
real parts. -/
theorem eq_17 {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (hN : 1 ≤ N)
    (T : Fin N → Matrix ι ι ℂ) (hT : ∀ k, IsDensityMatrix (T k))
    (P : Matrix ι ι ℂ) (hPP : P * P = P) (hPh : P.IsHermitian)
    (Q : Fin N → Matrix ι ι ℂ) (hQQ : ∀ k, Q k * Q k = Q k) (hQh : ∀ k, (Q k).IsHermitian)
    (hQT : ∀ k, Q k * T k = T k * Q k) :
    avgError T (sqrtMeas fun k => P * Q k * P) ≤
      (1 / (N : ℝ)) * ∑ k, (3 * (T k * (1 - P)).trace.re +
        ∑ k' ∈ Finset.univ.filter (· ≠ k), (P * T k * P * Q k').trace.re +
        (T k * (1 - Q k)).trace.re) := by sorry

end HolevoCQ
