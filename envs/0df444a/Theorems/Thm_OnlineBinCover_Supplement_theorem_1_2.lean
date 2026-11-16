-- Prove2me | Theorems.Thm_OnlineBinCover_Supplement_theorem_1_2
-- name    : OnlineBinCover.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:04:07.221626+00:00
-- url     : https://prove2.me/theorems/ee33dda3-1bf2-441e-a2c2-fc98bcb3ec3b
-- title:
--   Theorem 1.2 — order-oblivious: given $n$ and $B=\Theta(\mathrm{OPT}(I))$, $\mathbb E[A_{oo}(I;n,B)]\ge\mathrm{OPT}(I)-o(\mathrm{OPT}(I))$
-- statement:
--   **Order-oblivious bin covering.** There is a deterministic polynomial-time order-oblivious algorithm $A_{oo}$: one program $P$ of the exact real RAM, a sampling length $\kappa(n,B)\le n$ depending only on $n$ and $B$, and constants $C,e$, such that:
--
--   1. **(polynomial time)** told $n$, $\kappa(n,B)$ and $B$ in advance and fed all $n$ items one at a time, every run halts and the total work is at most $C(n+1)^e$, for every $n$, every real $B$, every $n$ sizes in $(0,1]$ and every arrival order;
--   2. **(guarantee)** for all constants $c_1,c_2>0$ there is a function $f$ with $f(m)/m\to0$ such that for every instance $I$ with sizes in $(0,1]$, every $B$ with $c_1\mathrm{OPT}(I)\le B\le c_2\mathrm{OPT}(I)$, and every adversary choosing the order of the non-sampled items after the first $\kappa(n,B)$ arrivals of a uniformly random permutation are revealed,
--   $$\mathbb E[A_{oo}(I;n,B)]\ \ge\ \mathrm{OPT}(I)-f(\mathrm{OPT}(I)),$$
--   where $A_{oo}(I;n,B)$ counts only the bins covered by the non-sampled items.
--
--   This is the common starting point of the random-order and single-sample prophet algorithms.
--
--   Differences from the source:
--   - reading: "deterministic polynomial-time algorithm" → a program of `PNormReg.Machine` without coin and power instructions (`DetANN.DetProgram`), with every per-item run halted and total work $\le C(n+1)^e$ for every $n$, real $B$, sizes in $(0,1]$ and arrival order; reason: the paper names no machine; the same reading as the published goal `theorem_1_3`
--   - reading: "Given $n$ and a value $B$"; "$k$ is chosen before observing any items" → a sampling length $\kappa(n,B)\le n$, a fixed function of $n$ and $B$; the initial memory holds $n$, $\kappa(n,B)$ and $B$; reason: the sampling length is part of the algorithm and depends only on the advance information; writing it in memory adds nothing beyond $n,B$
--   - reading: the sampling phase discards the first $k$ items (footnote 2: their bin never counts) → the program labels every item, but only the bins covered by the items at times $\ge\kappa(n,B)$ count (`coveredOn` over the complement of the sample); reason: footnote 2
--   - reading: "for every arrival order of the non-sampled items" → for every adversary map from the uniform permutation $\sigma$ to an arrival order whose first $\kappa(n,B)$ arrivals are those of $\sigma$; reason: the order may be chosen after the sample is revealed
--   - encoding: $B=\Theta(\mathrm{OPT}(I))$ → for all $c_1,c_2>0$, all $B$ with $c_1\mathrm{OPT}(I)\le B\le c_2\mathrm{OPT}(I)$, with $f$ chosen after $c_1,c_2$; reason: the hidden constants of $\Theta$ are arbitrary
--   - encoding: $o(\mathrm{OPT}(I))$ → one function $f$ with $f(m)/m\to0$, chosen before the instance; reason: the meaning of a uniform $o(\cdot)$
--   - encoding: a uniformly random permutation and $\mathbb E$ → the average over all $n!$ permutations (`avgPerm`); reason: uniform distribution
--   - encoding: a multiset $I$ and bins → a labelled size vector and integer bin labels; reason: OPT is invariant under relabelling
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Theorem 1.2, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_OnlineBinCover_Supplement_OrderOblivious

open Filter Topology

namespace OnlineBinCover.Supplement

/-- Theorem 1.2 (Order-oblivious bin covering), p.4 (PDF p.5); proof Section C, pp.30–31.
Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

Given `n` and a value `B = Θ(OPT(I))`, there is a deterministic polynomial-time order-oblivious
algorithm `A_oo`: one program `P` of the real RAM (`DetANN.DetProgram`) and one sampling length
`κ(n, B) ≤ n`, a function of `n` and `B` only, such that, told `n`, `κ(n,B)` and `B` in advance
and fed all items online, every run halts and the total work is at most `C (n+1)^e` for every `n`,
real `B`, sizes in `(0,1]` and arrival order. For all constants `c₁, c₂ > 0` (the hidden
constants of `B = Θ(OPT(I))`) there is one `f` with `f(m)/m → 0` such that for every instance,
every `B ∈ [c₁ OPT(I), c₂ OPT(I)]` and every adversary `adv` (which sees the uniform permutation
`σ` and returns an arrival order whose first `κ(n,B)` arrivals are those of `σ`),
`E_σ[A_oo(I; n, B)] ≥ OPT(I) − f(OPT(I))`, where only the bins covered by the non-sampled items
count (`ooValue`). -/
theorem theorem_1_2 : ∃ P : PNormReg.Program, DetANN.DetProgram P ∧ ∃ (C e : ℕ)
    (κ : ℕ → ℝ → ℕ), (∀ n B, κ n B ≤ n) ∧
    (∀ (n : ℕ) (B : ℝ) (s : Fin n → ℝ), ValidSizes s → ∀ π : Equiv.Perm (Fin n),
      (∀ t < n, (ooState P (C * (n + 1) ^ e) (κ n B) B s π (t + 1)).halted = true) ∧
      (ooState P (C * (n + 1) ^ e) (κ n B) B s π n).work ≤ C * (n + 1) ^ e) ∧
    ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
      ∃ f : ℕ → ℝ, Tendsto (fun m : ℕ => f m / (m : ℝ)) atTop (𝓝 0) ∧
      ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → ∀ B : ℝ,
        c₁ * (OPT s : ℝ) ≤ B → B ≤ c₂ * (OPT s : ℝ) →
        ∀ adv : Equiv.Perm (Fin n) → Equiv.Perm (Fin n),
          (∀ σ (t : Fin n), (t : ℕ) < κ n B → adv σ t = σ t) →
          (OPT s : ℝ) - f (OPT s) ≤
            DynamicOnlineLP.DLA.avgPerm
              (fun σ => (ooValue P (C * (n + 1) ^ e) (κ n B) B s (adv σ) : ℝ)) := by sorry

end OnlineBinCover.Supplement
