-- Prove2me | Theorems.Thm_OnlineBinCover_theorem_1_3
-- name    : OnlineBinCover.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:50:13.319925+00:00
-- url     : https://prove2.me/theorems/d5ba8446-ae38-401d-bf27-66fba78c1581
-- title:
--   Theorem 1.3 — deterministic polynomial-time online covering told neither $n$ nor OPT: $\mathbb E_\sigma[A_{ro}(I_\sigma)]\ge\mathrm{OPT}-o(\mathrm{OPT})$, ARR = ECR = 1
-- statement:
--   There is a deterministic online algorithm $A_{ro}$, given neither $n$ nor an estimate of $\mathrm{OPT}(I)$, namely one program $P$ of the real RAM fed the item sizes one at a time, and constants $C,k$, such that:
--
--   1. **(polynomial time)** for every $n$ and every sequence of $n$ sizes in $(0,1]$, each per-item run halts and the total work is at most $C(n+1)^k$;
--   2. **(random order)** for one function $f$ with $f(m)/m\to0$ and every instance $I$ with sizes in $(0,1]$,
--   $$\mathbb E_\sigma[A_{ro}(I_\sigma)]\ge\mathrm{OPT}(I)-f(\mathrm{OPT}(I));$$
--   3. **(ARR)** $\mathrm{ARR}(A_{ro})=1$;
--   4. **(ECR)** $\mathrm{ECR}(A_{ro})=1$ in the IID model, over every $n$ and every distribution on $(0,1]$.
--
--   This closes the gap between the previous random-order guarantee $0.501$ of Dual Next-Fit and the best possible ratio $1$.
--
--   Differences from the source:
--   - reading: "deterministic polynomial-time online algorithm" → a program of `PNormReg.Machine` without coin and power instructions, fed one size at a time, every run halted and total work $\le C(n+1)^k$ on every valid size sequence; reason: the paper names no machine; sizes are real numbers, so the exact real RAM; the paper counts total time (p.38)
--   - reading: "given neither $n$ nor an estimate of $\mathrm{OPT}(I)$" → only the current size is written into memory; no length, optimum or end marker; reason: what the program is told
--   - encoding: $o(\mathrm{OPT}(I))$ → one function $f$ with $f(m)/m\to0$, chosen before the instance; reason: the meaning of a uniform $o(\cdot)$
--   - encoding: $\mathrm{ARR}(A)=1$, $\mathrm{ECR}(A)=1$ (limits of infima, p.2) → `Tendsto` of `sInf` of the sets of ratios to $1$; reason: the definitions of p.2
--   - encoding: expectations in the IID model → lower Lebesgue integrals of nonnegative bounded functions, as reals; reason: equal to the expectation for measurable integrands
--   - encoding: bins → integer labels read from integer cell $-1$; every covered bin counts; reason: an assignment is a labelling
--   - encoding: a multiset $I$ and the random arrival sequence $I_\sigma$ → a labelled size vector $s$ and the sequence $s\circ\sigma$ averaged over all $n!$ permutations; reason: OPT and volume are invariant under relabelling
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Theorem 1.3, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_OnlineBinCover_Online
import Definitions.Def_OnlineBinCover_Ratios

open Filter Topology

namespace OnlineBinCover

/-- Theorem 1.3 (Random-order bin covering), p.5. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

There is a deterministic polynomial-time online algorithm `A_ro`, given neither `n` nor an estimate of
`OPT(I)`: one program `P` of the real RAM fed the sizes one at a time (layout `feedState`), with
every per-item run halted and total work at most `C (n+1)^k` on every sequence of sizes in `(0,1]`.
For one function `f` with `f(m)/m → 0` and every instance, `Eσ[A_ro(Iσ)] ≥ OPT(I) − f(OPT(I))`.
In particular `ARR(A_ro) = 1`, and the same algorithm has `ECR(A_ro) = 1` in the IID model, over every
`n` and every distribution on `(0,1]`. -/
theorem theorem_1_3 : ∃ P : PNormReg.Program, DetANN.DetProgram P ∧ ∃ C k : ℕ,
    (∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s →
      (∀ t < n, (feedState P (C * (n + 1) ^ k) (List.ofFn s) (t + 1)).halted = true) ∧
      (feedState P (C * (n + 1) ^ k) (List.ofFn s) n).work ≤ C * (n + 1) ^ k) ∧
    (∃ f : ℕ → ℝ, Tendsto (fun m : ℕ => f m / (m : ℝ)) atTop (𝓝 0) ∧
      ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s →
        (OPT s : ℝ) - f (OPT s) ≤ roAvg (fun n x => alg P (C * (n + 1) ^ k) x) s) ∧
    Tendsto (arrInf (fun n x => alg P (C * (n + 1) ^ k) x)) atTop (𝓝 1) ∧
    Tendsto (ecrInf (fun n x => alg P (C * (n + 1) ^ k) x)) atTop (𝓝 1) := by sorry

end OnlineBinCover
