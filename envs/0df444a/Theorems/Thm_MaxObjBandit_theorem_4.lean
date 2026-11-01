-- Prove2me | Theorems.Thm_MaxObjBandit_theorem_4
-- name    : MaxObjBandit.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:28.716306+00:00
-- url     : https://prove2.me/theorems/28ec72ff-8330-4ac7-a311-75126efde00e
-- title:
--   Theorem 4 — ADA-ETC regret bound for the max objective: explicit instance-dependent bound and worst-case $O(K^{1/3}T^{2/3}\sqrt{\log K})$ (corrected: ties broken by a fixed priority order)
-- statement:
--   Let ADA-ETC$_{K,T}$ be Algorithm 1 with $K$ arms and horizon $T$, with ties in its two argmaxes broken by a fixed priority order $\sigma$ on the arms. There is an absolute constant $C$ such that for all $1\le K<T$ and every priority order $\sigma$:
--
--   1. For every $\boldsymbol\nu\in\mathcal V$ whose optimal arm is unique, with arms labelled so that $\mu_1>\mu_2\ge\dots\ge\mu_K$, $\Delta_i=\mu_1-\mu_i$ (so $\Delta_1=0$) and $\tau=\lceil T^{2/3}/K^{2/3}\rceil$,
--   $$
--   \begin{aligned}
--   \mathrm{Reg}_T(\text{ADA-ETC}_{K,T},\boldsymbol\nu)\le{}&\mu_1\sum_{i=2}^K\min\Big(\frac{11}{\Delta_i^2}+\frac{16}{\Delta_i^2}\log^+\Big(\frac{T\Delta_i^3}{K}\Big)+\frac{24}{\Delta_i^2}\sqrt{\log^+\Big(\frac{T\Delta_i^3}{K}\Big)},\ \tau\Big)+\mu_1\tau\sum_{i=2}^K\min\Big(2,\frac{648K}{T\Delta_i^3}\Big)\\
--   &+\sum_{i=2}^K\exp\Big(-\frac{\tau\Delta_i^2}{2}\Big)T\Delta_i+\sum_{i=2}^K\min\Big(1,\frac{320K}{T\Delta_i^3}\Big)T(\Delta_i-\Delta_{i-1}).
--   \end{aligned}
--   $$
--   2. For every $\boldsymbol\nu\in\mathcal V$,
--   $$
--   \mathrm{Reg}_T(\text{ADA-ETC}_{K,T},\boldsymbol\nu)\le C\,K^{1/3}T^{2/3}\sqrt{\log K},
--   $$
--   that is, $\sup_{\boldsymbol\nu\in\mathcal V}\mathrm{Reg}_T(\text{ADA-ETC}_{K,T},\boldsymbol\nu)\le O(K^{1/3}T^{2/3}\sqrt{\log K})$.
--
--   The first two sums bound the regret from wasted pulls in the Explore phase, the last two the regret from committing to a wrong arm. Together with the lower bound of Theorem 2, the second clause shows that the minimax regret of the max objective is of order $T^{2/3}$ up to the factor $\sqrt{\log K}$.
--
--   **Formalization Note** Arms are `Fin K`; "$\mu_1>\mu_2\ge\dots\ge\mu_K$" is `Antitone ν.mean` with index $0$ strictly above every other index, and the bound reads the means with paper indices. The $O(\cdot)$ is one constant $C$ uniform in $K$, $T$, $\boldsymbol\nu$ and $\sigma$.
--
--   Differences from the source:
--   - correction: both argmaxes of Algorithm 1 break ties arbitrarily → ties broken by a fixed priority order $\sigma$ on the arms, for every $\sigma$ (`adaEtc K T hK σ`); reason: with arbitrary (history-dependent) tie-breaking the theorem is false: for $K=2$, $T\ge3$, $\nu_1=\nu_2=\delta_1$ both arms reach $\tau$ pulls with UCB = LCB = 1, the commit test $1>1$ never fires, and breaking the UCB tie toward the arm not pulled last gives regret $T-\lceil T/2\rceil\ge T/2-1$, which no $CK^{1/3}T^{2/3}\sqrt{\log K}$ bounds; for clause (i), $\nu_1=\delta_1$, $\nu_2=\mathrm{Bernoulli}(1-10^{-7})$, $T=10^4$ gives regret about $5000$ against a bound of about $879$
--   - reading: $\sup_{\boldsymbol\nu\in\mathcal V}\mathrm{Reg}_T\le O(K^{1/3}T^{2/3}\sqrt{\log K})$ → $\exists C,\ \forall K<T,\ \forall\sigma,\ \forall\boldsymbol\nu,\ \mathrm{Reg}_T\le CK^{1/3}T^{2/3}\sqrt{\log K}$; reason: the $O(\cdot)$ hides one absolute constant, uniform in $K$ and $T$, as the proof on pp.75–77 gives; a supremum bound is the same as a bound for every $\boldsymbol\nu$
--   - encoding: relabel arms so that $\mu_1>\mu_2\ge\dots\ge\mu_K$ → `Antitone ν.mean` and `ν.mean i < ν.mean 0` for every index $i\ne0$, with the bound read through `paperMean` (paper index $i$ is `Fin` index $i-1$, $\Delta_1=0$); reason: the same instances; the regret does not depend on the labelling
--   - reading: $\Pi_T$ is the set of all mappings from histories to arms → policies whose decision rules are measurable (`IsMeasurablePolicy`); reason: p.16 says that once a policy is fixed, $I_t$, $X_t$ and $n^i_t$ become well-defined random variables, which requires measurability; for a non-measurable rule $\mathcal R_T$ is undefined
--   - encoding: arms $1,\dots,K$ and rewards $U^i_n$ indexed from $n=1$ → arms `Fin K` (paper arm $i$ is index $i-1$) and a reward table `Fin K → ℕ → ℝ` with `ω i n` $=U^i_{n+1}$; reason: Lean indexing convention; the same objects
--   - encoding: Explore phase: pull each arm once at times $1,\dots,K$; the maximum in (4) for $K=1$ → arm $t$ at time $t$; for $K=1$ the maximum over no arms is $-\infty$, so (4) holds; reason: the order of the first $K$ pulls does not change the history's per-arm rewards or counts after time $K$; with one arm every rule pulls arm 1
--   - encoding: $1\le K$ implicit (a bandit has an arm) → `0 < K`; reason: $K=0$ makes $\mu_1$ and ADA-ETC meaningless
-- source:
--   Ozbay, Kamble, Maximal Objectives in the Multi-armed Bandit with Applications, arXiv:2006.06853v6, Theorem 4, p.22 (proof in Appendix C.1, pp.71–77)

import Mathlib
import Definitions.Def_MaxObjBandit_adaEtc

open MeasureTheory ProbabilityTheory

namespace MaxObjBandit

/-- **Theorem 4 (ADA-ETC performance)** (arXiv:2006.06853v6, Theorem 4, p.22; proof in
Appendix C.1, pp.71–77), with ties in ADA-ETC broken by a fixed priority order `σ`.

There is a constant `C` such that for all `1 ≤ K < T` and every priority order `σ` on the arms:
1. for every `ν ∈ 𝒱` whose optimal arm is unique and whose arms are labelled so that
   `µ₁ > µ₂ ≥ ⋯ ≥ µ_K`, `Reg_T(ADA-ETC_{K,T}, ν)` is at most the instance-dependent bound
   `theorem4Bound K T µ` (with `∆ᵢ = µ₁ − µᵢ`, `τ = ⌈T^{2/3}/K^{2/3}⌉`);
2. for every `ν ∈ 𝒱`, `Reg_T(ADA-ETC_{K,T}, ν) ≤ C K^{1/3} T^{2/3} √(log K)`, i.e.
   `sup_{ν∈𝒱} Reg_T(ADA-ETC_{K,T}, ν) ≤ O(K^{1/3}T^{2/3}√(log K))`.

**Formalization Note** Arms are `Fin K`; paper arm `i` is index `i − 1`, so "`µ₁ > µ₂ ≥ ⋯ ≥ µ_K`" is
`Antitone ν.mean` with index `0` strictly above every other index. The `O(·)` of the worst-case
clause is one constant `C`, uniform in `K`, `T`, `ν` and `σ`. The page breaks ties "arbitrarily"; this
statement fixes a priority order `σ` (any one) as the tie-breaking rule. -/
theorem theorem_4 :
    ∃ C : ℝ, ∀ (K T : ℕ) (hK : 0 < K), K < T → ∀ σ : Equiv.Perm (Fin K),
      (∀ ν : BanditInstance K,
        (∀ i : Fin K, (i : ℕ) ≠ 0 → ν.mean i < ν.mean ⟨0, hK⟩) → Antitone ν.mean →
          regret ν T (adaEtc K T hK σ) ≤ theorem4Bound K T (paperMean ν)) ∧
      (∀ ν : BanditInstance K,
        regret ν T (adaEtc K T hK σ)
          ≤ C * (K : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) * Real.sqrt (Real.log K)) := by sorry

end MaxObjBandit
