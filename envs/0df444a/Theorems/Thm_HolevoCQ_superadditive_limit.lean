-- Prove2me | Theorems.Thm_HolevoCQ_superadditive_limit
-- name    : HolevoCQ.superadditive_limit
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:49.78907+00:00
-- url     : https://prove2.me/theorems/918ce712-b0f8-4410-9f20-cb2f859b6460
-- title:
--   Eq. (3): superadditivity $C_n+C_m\le C_{n+m}$ and existence of $C=\lim C_n/n$
-- statement:
--   Let $i\mapsto S_i$ be a classical-quantum channel with finite input alphabet $A$ and density operators $S_i$ on a finite-dimensional Hilbert space $\mathcal H$. Let $C_n=\sup_{\pi,X}I_n(\pi,X)$ be the maximal Shannon information of the $n$-fold product channel. Then
--
--   1. $C_n+C_m\le C_{n+m}$ for all $n,m\ge0$;
--   2. the limit
--
--   $$
--   C=\lim_{n\to\infty}\frac{C_n}{n}
--   $$
--
--   exists, and it is the capacity of the channel.
--
--   Superadditivity is what makes the capacity well defined; the limit is then given by Fekete's lemma.
--
--   Differences from the source:
--   - encoding: input alphabet $A=\{1,\dots,a\}$, $D=\{1,\dots,d\}$, $\mathcal H=\mathbb C^d$, $\mathcal H^{\otimes n}$ → arbitrary finite types `A`, `D`; $\mathcal H=\mathbb C^D$; $\mathcal H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: Lean convention; every finite alphabet is in bijection with some finite type and conversely, so the instances are the same
--   - encoding: the alphabet $A$ is not said to be nonempty → `[Nonempty A]`; reason: with $A$ empty there is no probability distribution on $A$, so $C_n$ and $\max_\pi$ are undefined; the hypothesis excludes only that undefined case
--   - encoding: a decoding has "some finite output alphabet, which is not fixed" → output alphabet `Fin m` for every `m : ℕ`; reason: every finite output alphabet is in bijection with some `Fin m`
--   - encoding: $C_n=\sup_{\pi,X} I_n(\pi,X)$ → real `sSup` of the set of values $I_n(\pi,X)$; reason: the set is nonempty and bounded above by $n\log_2|A|$, so the real `sSup` is the supremum
--   - encoding: $I_n(\pi,X)$ by formula (1) → `mutualInfoBits` of the joint law $(u,j)\mapsto\pi_u\,\mathrm{Re}\,\mathrm{Tr}\,S_uX_j$ (`shannonInfo`), with the marginals recomputed; reason: for a probability vector $\pi$ and a POVM $X$ the marginals are $\pi_u$ and $\sum_k\pi_kP(j|k)$, so each summand equals that of (1), terms with $\pi_uP(j|u)=0$ vanishing on both sides; the traces involved are real
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (3), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_blockCap
import Definitions.Def_HolevoCQ_capacity

open Filter Topology QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (3), p.2: `C_n + C_m ≤ C_{n+m}` (superadditivity), hence the
limit `C = lim_{n→∞} C_n / n` exists.

**Formalization Note.** The second conjunct says that `C_n / n` converges to `capacity S`
(defined by `limUnder`), i.e. that the limit exists and is the capacity. Alphabets are finite
types; `[Nonempty A]` is assumed as everywhere in the mission. -/
theorem superadditive_limit {A D : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype D]
    [DecidableEq D] (S : A → Matrix D D ℂ) (hS : ∀ i, IsDensityMatrix (S i)) :
    (∀ n m : ℕ, blockCap S n + blockCap S m ≤ blockCap S (n + m)) ∧
      Tendsto (fun n : ℕ => blockCap S n / n) atTop (𝓝 (capacity S)) := by sorry

end HolevoCQ
