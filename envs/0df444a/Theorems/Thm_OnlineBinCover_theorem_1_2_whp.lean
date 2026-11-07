-- Prove2me | Theorems.Thm_OnlineBinCover_theorem_1_2_whp
-- name    : OnlineBinCover.theorem_1_2_whp
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:18.896385+00:00
-- url     : https://prove2.me/theorems/0ffa2565-73cf-488e-a1a3-25f820ab87dc
-- title:
--   Theorem 1.2 (high-probability form, Section C) — order-oblivious covering of $\mathrm{OPT}(I)-O(\mathrm{vol}(I)^{119/120})$ bins
-- statement:
--   The order-oblivious algorithm is given $n$ and an estimate $B$; it sets $p=B^{-1/20}$, takes the first $\lfloor pn\rfloor$ arrivals as its sample, chooses $\varepsilon$ by rounding $(p/\mathrm{vol}(I_p))^{1/24}$ down to a power of two, builds the blueprint from an LP solution on the sample, discards the sample, and assigns the remaining items by the rules of §4.
--
--   For all $c_1,c_2>0$ there are $C,c>0$ such that for every instance with sizes in $(0,1]$ and every $B$ with $c_1\mathrm{OPT}(I)\le B\le c_2\mathrm{OPT}(I)$, with probability at least
--
--   $$1-\exp\!\big(-c\,\mathrm{vol}(I)^{3/40}\big)$$
--
--   over the arrival order, the following holds for every order of the non-sampled items (even one chosen after the sample is revealed), every LP solution meeting Lemma 2.2 on the sample and every tie-breaking: at least
--
--   $$\mathrm{OPT}(I)-C\,\mathrm{vol}(I)^{119/120}$$
--
--   blueprint bins are covered using only the non-sampled items.
--
--   This is the form of Theorem 1.2 that the known-length analysis (Theorem D.1) applies to two fixed sample lengths; with the nonnegativity of the covered count it gives Theorem 1.2's expectation bound.
--
--   Differences from the source:
--   - reading: Theorem 1.2: $\mathbb E[A_{oo}(I;n,B)]\ge\mathrm{OPT}(I)-o(\mathrm{OPT}(I))$ → the high-probability bound established in its proof (Section C, p.31); reason: the form Theorem D.1 uses; it implies the expectation bound
--   - encoding: $B=\Theta(\mathrm{OPT}(I))$ → for all $c_1,c_2>0$, $B\in[c_1\mathrm{OPT}(I),c_2\mathrm{OPT}(I)]$, constants chosen after $c_1,c_2$; reason: the meaning of $\Theta$
--   - generalization: $A$ counts all covered bins → the number of covered blueprint bins; reason: each covered blueprint bin is a covered bin, so the bound implies the source's for every placement of the overflow items
--   - generalization: the LP solution and the assignment choices of the algorithm → every LP solution meeting the guarantee of Lemma 2.2 on the sample and every tie-breaking priority, inside the event; reason: the proof uses only that guarantee; specializes to any fixed LP algorithm and tie-breaking
--   - encoding: "for every arrival order of the non-sampled items" → for every duplicate-free list of the non-sampled items, quantified inside the event; reason: the order may depend on the sample (p.4)
--   - encoding: "place the item in an arbitrary bin" → an overflow bin outside the blueprint; reason: only blueprint bins are counted
--   - encoding: $O(\cdot)$, $\Omega(\cdot)$ → absolute constants $C,c>0$ chosen before $\varepsilon$, $p$ and the instance; reason: the paper writes the dependence on $K,\varepsilon,p$ explicitly
--   - encoding: ties resolved consistently across $I$ and its subsets → ties broken by the item label; reason: a consistent rule, as p.6 requires
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Theorem 1.2, p.4 (PDF p.5); proof in Section C, pp.30–31 (PDF pp.31–32)

import Mathlib
import Definitions.Def_OnlineBinCover_Blueprint

namespace OnlineBinCover

/-- Theorem 1.2 (Order-oblivious bin covering), p.4, in the high-probability form of its proof
(Section C, pp.30–31). Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

Given `n` and `B = Θ(OPT(I))`, the order-oblivious algorithm sets `p = B^{-1/20}`, takes the first
`⌊pn⌋` arrivals as the sample, chooses `ε` by rounding `(p/vol(Ip))^{1/24}` down to a power of two,
builds the blueprint and discards the sample. For all `c₁, c₂ > 0` there are `C, c > 0` such that for
every instance with sizes in `(0,1]` and every `B ∈ [c₁ OPT(I), c₂ OPT(I)]`, with probability at least
`1 − exp(−c vol(I)^{3/40})` over the sample, for **every** arrival order of the remaining items
(possibly chosen after the sample is revealed), every LP solution meeting Lemma 2.2 on the sample
and every tie-breaking, at least `OPT(I) − C vol(I)^{119/120}` blueprint bins are covered using only
the non-sampled items. -/
theorem theorem_1_2_whp : ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → ∀ B : ℝ, c₁ * (OPT s : ℝ) ≤ B →
      B ≤ c₂ * (OPT s : ℝ) →
      1 - Real.exp (-(c * vol s ^ ((3 : ℝ) / 40))) ≤
        DynamicOnlineLP.DLA.probPerm (fun σ : Equiv.Perm (Fin n) =>
          ∀ rest : List (Fin n), rest.Nodup →
            rest.toFinset = Finset.univ \ smp σ ⌊B ^ (-(1 : ℝ) / 20) * n⌋₊ →
          ∀ x : (Fin (Kof (epsChoice (B ^ (-(1 : ℝ) / 20))
              (volOn s (smp σ ⌊B ^ (-(1 : ℝ) / 20) * n⌋₊)))) → ℕ) →₀ ℝ,
            LPSpec s (smp σ ⌊B ^ (-(1 : ℝ) / 20) * n⌋₊)
              (epsChoice (B ^ (-(1 : ℝ) / 20)) (volOn s (smp σ ⌊B ^ (-(1 : ℝ) / 20) * n⌋₊))) x →
          ∀ prioL prioS,
            (OPT s : ℝ) - C * vol s ^ ((119 : ℝ) / 120) ≤
              (phaseRun s (smp σ ⌊B ^ (-(1 : ℝ) / 20) * n⌋₊)
                (epsChoice (B ^ (-(1 : ℝ) / 20)) (volOn s (smp σ ⌊B ^ (-(1 : ℝ) / 20) * n⌋₊)))
                (B ^ (-(1 : ℝ) / 20)) x prioL prioS rest : ℝ)) := by sorry

end OnlineBinCover
