-- Prove2me | Theorems.Thm_HolevoCQ_decoder_subPOVM
-- name    : HolevoCQ.decoder_subPOVM
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:11.392779+00:00
-- url     : https://prove2.me/theorems/c0eca852-d0df-4ebe-8559-80083b3799eb
-- title:
--   §4: the decision operators (11) satisfy $\sum_uX_u\le I$
-- statement:
--   Let $B_1,\dots,B_N$ be positive operators on a finite-dimensional Hilbert space and put
--
--   $$
--   X_u=\Big(\sum_{u'=1}^NB_{u'}\Big)^{-1/2}B_u\Big(\sum_{u'=1}^NB_{u'}\Big)^{-1/2},
--   $$
--
--   where $Y^{-1/2}$ is the generalized inverse of $Y^{1/2}$ (zero on $\mathrm{Ker}\,Y$). Then every $X_u$ is positive and
--
--   $$
--   \sum_{u=1}^NX_u\le I .
--   $$
--
--   With $B_u=PP_uP$ this says that Holevo's decision rule (11) is a code in the sense of p.2.
--
--   Differences from the source:
--   - generalization: $B_u=PP_uP$ with $P$ from (6) and $P_u$ from (8) → arbitrary positive semidefinite $B_u$ on an arbitrary finite-dimensional space; reason: the paper's $PP_uP$ are positive operators on $\mathcal H^{\otimes n}$, so the Lean statement contains the paper's case
--   - generalization: conclusion $\sum_uX_u\le I$ → conclusion also asserts $X_u\ge0$ for every $u$ (`IsSubPOVM`); reason: positivity of each $X_u$ is required for (11) to be a code (p.2) and is immediate; Lean asserts more than the printed sentence
--   - encoding: generalized inverse of $X^{1/2}$ → `cfc` of $x\mapsto(\sqrt x)^{-1}$ with $(\sqrt0)^{-1}=0$; reason: equal to $0$ on the kernel and $(X^{1/2})^{-1}$ on its orthogonal complement, the paper's definition
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, §4, p.4

import Mathlib
import Definitions.Def_HolevoCQ_IsSubPOVM
import Definitions.Def_HolevoCQ_sqrtMeas

open scoped ComplexOrder

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, §4, p.4: the operators
`X_u = (Σ_{u'} B_{u'})^{−1/2} B_u (Σ_{u'} B_{u'})^{−1/2}` of (11), with `X^{−1/2}` the generalized
inverse of `X^{1/2}`, are positive and satisfy `Σ_{u=1}^N X_u ≤ I`.

**Formalization Note.** Stated for arbitrary positive semidefinite `B_u` on any finite-dimensional
space; the paper's case is `B_u = P P_u P`. Positivity of each `X_u` (needed for a code) is part of
the conclusion `IsSubPOVM`. -/
theorem decoder_subPOVM {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (B : Fin N → Matrix ι ι ℂ) (hB : ∀ k, (B k).PosSemidef) :
    IsSubPOVM (sqrtMeas B) := by sorry

end HolevoCQ
