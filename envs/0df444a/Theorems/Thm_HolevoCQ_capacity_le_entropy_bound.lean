-- Prove2me | Theorems.Thm_HolevoCQ_capacity_le_entropy_bound
-- name    : HolevoCQ.capacity_le_entropy_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:42.928478+00:00
-- url     : https://prove2.me/theorems/a419eb22-a41e-4536-aed4-a75ecc349a61
-- title:
--   §2: $C_n\le n\max_\pi\Delta H(\pi)$, hence $C\le\max_\pi\Delta H(\pi)$
-- statement:
--   Let $i\mapsto S_i$ be a classical-quantum channel with finite input alphabet $A$ and density operators $S_i$ on a finite-dimensional Hilbert space. For every $n\ge0$,
--
--   $$
--   C_n\le n\cdot\max_\pi\Delta H(\pi),
--   $$
--
--   where $\Delta H(\pi)=H(\sum_i\pi_iS_i)-\sum_i\pi_iH(S_i)$ and the maximum is over the distributions on $A$. Dividing by $n$ and letting $n\to\infty$ gives the upper half of Holevo's Theorem, $C\le\max_\pi\Delta H(\pi)$; the page derives it from the entropy bound [7] and the additivity property of the Appendix.
--
--   Differences from the source:
--   - encoding: input alphabet $A=\{1,\dots,a\}$, $D=\{1,\dots,d\}$, $\mathcal H=\mathbb C^d$, $\mathcal H^{\otimes n}$ → arbitrary finite types `A`, `D`; $\mathcal H=\mathbb C^D$; $\mathcal H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: Lean convention; every finite alphabet is in bijection with some finite type and conversely, so the instances are the same
--   - encoding: the alphabet $A$ is not said to be nonempty → `[Nonempty A]`; reason: with $A$ empty there is no probability distribution on $A$, so $C_n$ and $\max_\pi$ are undefined; the hypothesis excludes only that undefined case
--   - encoding: a decoding has "some finite output alphabet, which is not fixed" → output alphabet `Fin m` for every `m : ℕ`; reason: every finite output alphabet is in bijection with some `Fin m`
--   - encoding: $C_n=\sup_{\pi,X} I_n(\pi,X)$ → real `sSup` of the set of values $I_n(\pi,X)$; reason: the set is nonempty and bounded above by $n\log_2|A|$, so the real `sSup` is the supremum
--   - encoding: $\max_\pi\Delta H(\pi)$ → real supremum `⨆` over the probability simplex on `A`; reason: nonempty, bounded above and attained, so the supremum is the maximum
--   - generalization: $C\le\max_\pi\Delta H(\pi)$ → $C_n\le n\max_\pi\Delta H(\pi)$ for every $n$; reason: dividing by $n$ and passing to the limit (3) gives the paper's inequality; the per-$n$ bound is what the entropy bound and the Appendix give
--   - encoding: $I_n(\pi,X)$ by formula (1) → `mutualInfoBits` of the joint law $(u,j)\mapsto\pi_u\,\mathrm{Re}\,\mathrm{Tr}\,S_uX_j$ (`shannonInfo`), with the marginals recomputed; reason: for a probability vector $\pi$ and a POVM $X$ the marginals are $\pi_u$ and $\sum_k\pi_kP(j|k)$, so each summand equals that of (1), terms with $\pi_uP(j|u)=0$ vanishing on both sides; the traces involved are real
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, §2, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_holevoChi
import Definitions.Def_HolevoCQ_blockCap

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, §2, p.2: "The entropy bound [7] combined with an additivity property
proved in Appendix implies `C ≤ max_π ΔH(π)`." Stated in the form the argument gives:
`C_n ≤ n · max_π ΔH(π)` for every `n`, which yields `C ≤ max_π ΔH(π)` after dividing by `n`.

**Formalization Note.** The maximum is the real supremum over the probability simplex on `A`
(nonempty and bounded above). -/
theorem capacity_le_entropy_bound {A D : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype D] [DecidableEq D] (S : A → Matrix D D ℂ) (hS : ∀ i, IsDensityMatrix (S i)) :
    ∀ n : ℕ, blockCap S n ≤ n * ⨆ π : stdSimplex ℝ A, holevoChi S π := by sorry

end HolevoCQ
