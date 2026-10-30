-- Prove2me | Theorems.Thm_HolevoCQ_theorem_capacity
-- name    : HolevoCQ.theorem_capacity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:53.543482+00:00
-- url     : https://prove2.me/theorems/ff2e38e9-4544-4182-83c1-4f53d70b2afc
-- title:
--   Theorem (5): $C=\max_\pi[H(\sum_i\pi_iS_i)-\sum_i\pi_iH(S_i)]$
-- statement:
--   Let $\mathcal H$ be a finite-dimensional Hilbert space, $A$ a finite input alphabet and $i\mapsto S_i$ an arbitrary family of density operators on $\mathcal H$ (possibly mixed and non-commuting). Let $C_n$ be the maximal Shannon information of the $n$-fold product channel, over all distributions on words and all measurements on $\mathcal H^{\otimes n}$, and let $C=\lim_nC_n/n$ be the capacity (3). Then
--
--   $$
--   C=\max_\pi\Big[H\Big(\sum_{i\in A}\pi_iS_i\Big)-\sum_{i\in A}\pi_iH(S_i)\Big],
--   $$
--
--   where $H$ is the von Neumann entropy (binary logarithm) and the maximum is over the probability distributions $\pi$ on $A$. Precisely: the maximum is attained at some $\pi_0$, $C_n/n$ converges to its value, and the capacity equals it.
--
--   This is the classical capacity theorem for classical-quantum channels with general signal states (Holevo; Schumacher–Westmoreland), extending the pure-state result of Hausladen, Jozsa, Schumacher, Westmoreland and Wootters.
--
--   Differences from the source:
--   - encoding: input alphabet $A=\{1,\dots,a\}$, $D=\{1,\dots,d\}$, $\mathcal H=\mathbb C^d$, $\mathcal H^{\otimes n}$ → arbitrary finite types `A`, `D`; $\mathcal H=\mathbb C^D$; $\mathcal H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: Lean convention; every finite alphabet is in bijection with some finite type and conversely, so the instances are the same
--   - encoding: the alphabet $A$ is not said to be nonempty → `[Nonempty A]`; reason: with $A$ empty there is no probability distribution on $A$, so $C_n$ and $\max_\pi$ are undefined; the hypothesis excludes only that undefined case
--   - encoding: a decoding has "some finite output alphabet, which is not fixed" → output alphabet `Fin m` for every `m : ℕ`; reason: every finite output alphabet is in bijection with some `Fin m`
--   - encoding: $C_n=\sup_{\pi,X} I_n(\pi,X)$ → real `sSup` of the set of values $I_n(\pi,X)$; reason: the set is nonempty and bounded above by $n\log_2|A|$, so the real `sSup` is the supremum
--   - generalization: $C=\lim_nC_n/n$ with the existence of the limit taken from superadditivity (p.2) → the conclusion also asserts that $C_n/n$ converges to the maximum; reason: Lean asserts more; dropping the clause leaves the paper's identity $C=\max_\pi\Delta H(\pi)$
--   - encoding: $I_n(\pi,X)$ by formula (1) → `mutualInfoBits` of the joint law $(u,j)\mapsto\pi_u\,\mathrm{Re}\,\mathrm{Tr}\,S_uX_j$ (`shannonInfo`), with the marginals recomputed; reason: for a probability vector $\pi$ and a POVM $X$ the marginals are $\pi_u$ and $\sum_k\pi_kP(j|k)$, so each summand equals that of (1), terms with $\pi_uP(j|u)=0$ vanishing on both sides; the traces involved are real
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, Theorem, eq. (5), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_holevoChi
import Definitions.Def_HolevoCQ_blockCap
import Definitions.Def_HolevoCQ_capacity

open Filter Topology QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, Theorem, eq. (5), p.3: the capacity of the quantum communication channel
with arbitrary signal states `S_i` is
`C = max_π [H(Σ_{i∈A} π_i S_i) − Σ_{i∈A} π_i H(S_i)]`.

**Formalization Note.** `H = ℂ^D` with `D` finite, the input alphabet `A` is finite and nonempty,
the `S_i` are arbitrary density matrices (mixed, non-commuting). The conclusion states that the
maximum over the probability simplex is attained at some `π₀`, that `C_n / n` converges to its
value (so the limit (3) exists), and that the capacity `C` of (3) equals it. `C_n` is the
supremum over all laws on words and all POVMs on `H^{⊗n}` (`blockCap`); `H` is the binary
`vnEntropy`. -/
theorem theorem_capacity {A D : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype D]
    [DecidableEq D] (S : A → Matrix D D ℂ) (hS : ∀ i, IsDensityMatrix (S i)) :
    ∃ π₀ ∈ stdSimplex ℝ A,
      (∀ π ∈ stdSimplex ℝ A, holevoChi S π ≤ holevoChi S π₀) ∧
      Tendsto (fun n : ℕ => blockCap S n / n) atTop (𝓝 (holevoChi S π₀)) ∧
      capacity S = holevoChi S π₀ := by sorry

end HolevoCQ
