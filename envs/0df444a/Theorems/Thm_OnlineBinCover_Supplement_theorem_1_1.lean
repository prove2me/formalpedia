-- Prove2me | Theorems.Thm_OnlineBinCover_Supplement_theorem_1_1
-- name    : OnlineBinCover.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:37:19.991738+00:00
-- url     : https://prove2.me/theorems/e0bd2272-f8be-43f1-aa1d-b6c699cea0cc
-- title:
--   Theorem 1.1 — AoS: a deterministic polynomial-time algorithm covers $\mathrm{OPT}(I)-o(\mathrm{OPT}(I))$ bins in expectation when $p=\Omega(\mathrm{vol}(I)^{-1/20})$
-- statement:
--   **Adversarial order with a sample.** There is a deterministic polynomial-time algorithm $A_{\mathrm{AoS}}$, one program $P$ of the exact real RAM and constants $C,e$, such that:
--
--   1. **(polynomial time)** for every $n$, every $p\in(0,1)$, every $n$ sizes in $(0,1]$ and every arrangement, the offline run and every online run halt and the total work is at most $C(n+1)^e$;
--   2. **(guarantee)** for every constant $c>0$ there is a function $f$ with $f(m)/m\to0$ such that for every instance $I$ with sizes in $(0,1]$, every sampling fraction $p\in(0,1)$ with $p\ge c\,\mathrm{vol}(I)^{-1/20}$, and every adversary choosing the listing of the sample and the order of the non-sampled items after seeing the sample,
--   $$\mathbb E[A_{\mathrm{AoS}}(I)]\ \ge\ \mathrm{OPT}(I)-f(\mathrm{OPT}(I)),$$
--   where the sample is a uniformly random subset of $\lfloor pn\rfloor$ items and sample items count in $A_{\mathrm{AoS}}$.
--
--   Thus a small fraction of the input suffices to learn an asymptotically optimal covering against an adversarial order.
--
--   Differences from the source:
--   - reading: "deterministic polynomial-time algorithm" → a program of `PNormReg.Machine` without coin and power instructions (`DetANN.DetProgram`), with the offline run and every online run halted and total work $\le C(n+1)^e$ for every $n$, $p\in(0,1)$, sizes in $(0,1]$ and arrangement; reason: the paper names no machine; the same reading as the published goal `theorem_1_3`
--   - reading: the AoS model (knows $n$ and $p$; sample offline; remaining items online) → initial memory $n,\lfloor pn\rfloor,p$ and the sample sizes; one offline run; sample labels read from integer cells $-2-j$ before the first online item; online items fed one at a time; reason: what the algorithm is told, and when its decisions become irrevocable
--   - reading: "for every adversarial ordering of the non-sampled items" → for every adversary map from the uniform permutation $\sigma$ to an arrangement listing the sample $\mathrm{smp}(\sigma,\lfloor pn\rfloor)$ first (in any order) and the other items after (in any order); reason: the order may be chosen after the sample is revealed; a deterministic algorithm gains nothing from an adversary that sees less
--   - encoding: $p=\Omega(\mathrm{vol}(I)^{-1/20})$ → for every $c>0$, all $p\ge c\,\mathrm{vol}(I)^{-1/20}$, with $f$ chosen after $c$; reason: the hidden constant of $\Omega$ is arbitrary and the $o(\cdot)$ may depend on it
--   - encoding: $o(\mathrm{OPT}(I))$ → one function $f$ with $f(m)/m\to0$, chosen before the instance; reason: the meaning of a uniform $o(\cdot)$, as in `theorem_1_3`
--   - encoding: a uniformly random subset $I_p$ of size $\lfloor pn\rfloor$ and $\mathbb E$ → the first $\lfloor pn\rfloor$ positions of a uniform permutation (`smp`), averaged over all $n!$ permutations (`avgPerm`); reason: same distribution of the sample
--   - encoding: a multiset $I$ and bins → a labelled size vector and integer bin labels; every covered bin counts; reason: OPT and volume are invariant under relabelling; an assignment is a labelling
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Theorem 1.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_OnlineBinCover_Supplement_AoS

open Filter Topology

namespace OnlineBinCover.Supplement

/-- Theorem 1.1 (Adversarial order with a sample), p.3 (PDF p.4); proof Section B.4, p.26.
Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

There is a deterministic polynomial-time algorithm `A_AoS`: one program `P` of the real RAM
(`DetANN.DetProgram`) run in the AoS protocol (`aosValue`), with the offline run and every online
run halted and total work at most `C (n+1)^e` for every `n`, `p ∈ (0,1)`, sizes in `(0,1]` and
arrangement. For every constant `c > 0` (the hidden constant of `p = Ω(vol(I)^{−1/20})`) there is
one function `f` with `f(m)/m → 0` such that for every instance `I`, every `p ∈ (0,1)` with
`p ≥ c·vol(I)^{−1/20}` and every adversary `adv` (which sees the uniform permutation `σ` and
returns an arrangement listing the sample `smp σ ⌊pn⌋` first, in any order, followed by the
remaining items in any order), `E_σ[A_AoS(I)] ≥ OPT(I) − f(OPT(I))`.

**Formalization Note.** The sample is the set of the first `⌊pn⌋` positions of a uniformly random
permutation (published `smp`), the expectation the published `avgPerm`. `vol(I)^{−1/20}` is
`Real.rpow`; for `n = 0` it is `0`. -/
theorem theorem_1_1 : ∃ P : PNormReg.Program, DetANN.DetProgram P ∧ ∃ C e : ℕ,
    (∀ (n : ℕ) (p : ℝ), 0 < p → p < 1 → ∀ (s : Fin n → ℝ), ValidSizes s →
      ∀ π : Equiv.Perm (Fin n),
        (aosOffline P (C * (n + 1) ^ e) s p π).halted = true ∧
        (∀ t < n - sampleSize n p, (aosState P (C * (n + 1) ^ e) s p π (t + 1)).halted = true) ∧
        (aosState P (C * (n + 1) ^ e) s p π (n - sampleSize n p)).work ≤ C * (n + 1) ^ e) ∧
    ∀ c : ℝ, 0 < c → ∃ f : ℕ → ℝ, Tendsto (fun m : ℕ => f m / (m : ℝ)) atTop (𝓝 0) ∧
      ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → ∀ p : ℝ, 0 < p → p < 1 →
        c * vol s ^ (-(1 / 20 : ℝ)) ≤ p →
        ∀ adv : Equiv.Perm (Fin n) → Equiv.Perm (Fin n),
          (∀ σ, smp (adv σ) (sampleSize n p) = smp σ (sampleSize n p)) →
          (OPT s : ℝ) - f (OPT s) ≤
            DynamicOnlineLP.DLA.avgPerm
              (fun σ => (aosValue P (C * (n + 1) ^ e) s p (adv σ) : ℝ)) := by sorry

end OnlineBinCover.Supplement
