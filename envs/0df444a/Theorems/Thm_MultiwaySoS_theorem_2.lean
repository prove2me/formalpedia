-- Prove2me | Theorems.Thm_MultiwaySoS_theorem_2
-- name    : MultiwaySoS.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:01.615278+00:00
-- url     : https://prove2.me/theorems/3879a064-bfad-4359-92b5-63a67c3fad1e
-- title:
--   Theorem 2 (corrected: reward scale $R$, $1+\log t$) — the Sum-of-Squares algorithm has any-time regret $O(1/\delta)$, and $O(\log t/\delta)$ in general
-- statement:
--   There are constants $C>0$ and $a,b\in\mathbb N$ with the following property. Consider any multiway matching instance with $n$ resource types (offline, online-queueable and online-nonqueueable), any basis $\mathcal M_+$ and cyclic orders $\sigma_m$, and any non-stationary arrival process satisfying the hypotheses of Theorem 2: arrivals $I^t$ drawn from predictable distributions $\lambda^t$; Assumption 1 (almost surely $\bar\lambda$ satisfies GPG$_{\epsilon_0}$ with basis $\mathcal M_+$, $\epsilon_0>0$); offline inventories $\bar\lambda_iT$ with $A^T_i=\bar\lambda_iT$; and Assumption 2 (smoothed GPG$_{\delta,\tau}$ with $0<\delta\le\epsilon_0$ and window $\tau\in\mathbb N$). Run the Sum-of-Squares algorithm (Algorithm 2) with any arg-min commit rule, let $R\ge\max_{m\in\mathcal M_+}r_m$, and put $\kappa(n,\tau)=C(1+n)^a(1+\tau)^b$. Then for every $t\in[1,T]$, with $X^t$ the true matches and $A^t$ the cumulative arrivals:
--
--   1. if no configuration of $\mathcal M_+$ contains both an online-queueable and an online-nonqueueable resource,
--   $$\mathbb E\Big[\sum_mr_mX^t_m\Big]\ge\mathbb E[\mathrm{OPT}(A^t)]-\frac{R\,\kappa(n,\tau)}{\delta};$$
--   2. in every case,
--   $$\mathbb E\Big[\sum_mr_mX^t_m\Big]\ge\mathbb E[\mathrm{OPT}(A^t)]-\frac{R\,\kappa(n,\tau)}{\delta}(1+\log t).$$
--
--   The constants do not depend on $T$, $\delta$, the rewards, the instance or the arrival process. The rate $1/\delta$ in the first clause is the one shown to be necessary for online-queueable resources by Kerimov et al. (2021).
--
--   Differences from the source:
--   - correction: regret bounds $\kappa_1(n,\tau)/\delta$ and $(\kappa_2(n,\tau)/\delta)\log t$ with $\kappa_j$ depending on $n,\tau$ only → $R\,\kappa(n,\tau)/\delta$ and $R\,\kappa(n,\tau)(1+\log t)/\delta$ for any $R\ge\max_{m\in\mathcal M_+}r_m$; reason: regret scales with the rewards: $n=2$, online-queueable types, $a=\{1,2\}$ with reward $R$, $b=\{1\}$, $c=\{2\}$ with reward $0$, i.i.d. $\lambda^t=\hat\lambda^t=\bar\lambda=(2/3,1/3)$, $\tau=0$, $\epsilon_0=1/12$, $\delta=1/24$, $\mathcal M_+=\{a,b\}$ satisfies every hypothesis and has regret $2R/9$ at $t=2$, unbounded in $R$
--   - correction: $(\kappa_2(n,\tau)/\delta)\log t$ → $R\,\kappa(n,\tau)(1+\log t)/\delta$; reason: the printed bound is $0$ at $t=1$; with type 1 online-queueable, type 2 online-nonqueueable, $a=\{1,2\}$ with reward $3$, $b=\{1\}$, $c=\{2\}$ with reward $0$, $d=\{1\}$ with reward $1$, $\bar\lambda=(1/3,2/3)$ i.i.d., $\mathcal M_+=\{a,c\}$, the regret at $t=1$ is $1/3>0$
--   - generalization: $0<\delta<\epsilon_0$ (Assumption 2, Theorem 2) → $0<\delta\le\epsilon_0$; reason: p.17 (example 2) and p.18 use $\delta=\epsilon_0$; the range contains the printed one
--   - generalization: clause 2 stated "if there are feasible configurations in $\mathcal M_+$ which contain resources from both" → clause 2 for every instance; reason: the bound holds in both cases; it specializes to the printed case
--   - reading: "the distribution $\lambda^t$ from which the type $I^t$ is sampled is itself a random quantity, which is $\mathcal F^{t-1}$-measurable. Conditioned on the sequence $\{\lambda^t\}$, $\{I^t\}$ are assumed to be mutually independent" (p.15) → $P(I^t=i\mid\mathcal F^{t-1})=\lambda^t_i$, written as $P(A\cap\{I^t=i\})=\int_A\lambda^t_i\,dP$ for $A\in\mathcal F^{t-1}$; reason: this is the sampling sentence of the page; the conditional-independence sentence is not assumed separately, because it would add no constraint the proof uses once each $I^t$ is drawn from the predictable $\lambda^t$
--   - reading: Assumption 1: "almost surely $\bar\lambda$ satisfies GPG$_{\epsilon_0}$"; "we fix an optimal basic feasible solution $x^*$ and its basis $\mathcal M_+$" (p.16) → $\bar\lambda$ and $x^*$ are random, the basis $\mathcal M_+$ is one fixed set, GPG holds almost surely; Assumption 2 and the offline requirement hold almost surely; reason: Algorithm 2 needs a fixed $\mathcal M_+$; a deterministic $\bar\lambda$ is the constant case, so this reading is the stronger statement
--   - reading: Definition 2 (GPG), clause 2 "with $\mathcal M_+$ as the basic activities", and clause 1 → the support of the solution is exactly $\mathcal M_+$, whose columns are linearly independent; clause 1 is not written; reason: basic activities are the non-zero components (p.4); clause 1 follows from linear independence
--   - reading: $m^t=\arg\min_m\{\Delta\Phi_m(\mathscr Q^{t-1}_m,I^t)\}$ with no tie-breaking rule → every commit rule that returns a minimizer, possibly depending on the time and the whole state; reason: ties are arbitrary in the paper; a statement for every such rule covers each of them
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
--   - reading: second line of (10): $Q_{i^\prime m}+\mathbb 1\{i^\prime=i\}<M_{im}$ → $Q_{i^\prime m}+\mathbb 1\{i^\prime=i\}<M_{i^\prime m}$; reason: obvious intent; both entries equal $1$ for $i,i^\prime\in\mathcal I(m)$
--   - encoding: "$\kappa(n,\tau)$ is a constant that is polynomial in $n,\tau$, independent of $T$" → $C(1+n)^a(1+\tau)^b$ with $C,a,b$ chosen before every other quantity; reason: every polynomial bound in $n,\tau$ is dominated by such a form and conversely; the $1+$ keeps the bound positive at $n=0$ or $\tau=0$
--   - encoding: $\mathrm{OPT}(A^t)$, the optimal value of the LP → `sSup` of the objective over the feasible set; reason: for $A^t\ge0$ the set is nonempty (discard singletons) and bounded above under GPG (weak duality), so the supremum is the LP value
--   - encoding: types $[n]$ split into the intervals $\mathcal I^{\rm off},\mathcal I^{\rm on\text{-}q},\mathcal I^{\rm on\text{-}nq}$; configurations $\mathcal M$ → `Fin n` with a labelling `kind`, configurations `Fin d`, time $1$-based, queue lengths in $\mathbb Z$; reason: a renumbering of the types; same instances
--   - encoding: $\sum_{s=1}^{t-2\tau}\hat\lambda^s$ in Assumption 2 → `Finset.Icc 1 (t - 2 * τ)` with truncated subtraction; reason: the sum is empty for $t\le2\tau$, the paper's meaning; no instance changes
--   - encoding: a probability space carrying the arrival process → $\Omega$ in `Type` (universe $0$); reason: $C,a,b$ are chosen before $\Omega$, and the regret depends only on the law of the finite sequence $(I^1,\dots,I^t)$, which is realized on a space in `Type`
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Theorem 2, p.18 (proof pp.24–25)

import Mathlib
import Definitions.Def_MultiwaySoS_Setting

open MeasureTheory

namespace MultiwaySoS

/-- Theorem 2 (arXiv:2112.04622v3, p.18), corrected: the any-time regret of the Sum-of-Squares
algorithm.

There are constants `C > 0` and `a, b ∈ ℕ` such that for every instance (`n` types, `d`
configurations), every basis `M₊ = B` and cyclic orders `σ`, every probability space and arrival
process satisfying the hypotheses of Theorem 2 (`IsSetting`: the arrival model, Assumption 1 with
`ϵ₀ > 0`, Smoothed `GPG_{δ,τ}` with `0 < δ ≤ ϵ₀`, offline inventories `λ̄_i T`), every arg-min
commit rule, every `R ≥ max_{m ∈ M₊} r_m`, and every `t ∈ [1, T]`, with
`κ(n, τ) = C(1 + n)^a (1 + τ)^b`:
1. if no configuration of `M₊` contains both an online-queueable and an online-nonqueueable type,
   `E[OPT(A^t)] − E[∑_m r_m X^t_m] ≤ R κ(n, τ)/δ`;
2. in every case, `E[OPT(A^t)] − E[∑_m r_m X^t_m] ≤ R κ(n, τ)(1 + log t)/δ`.

`X^t` are the true matches of Algorithm 2 and `A^t` the cumulative arrivals. The paper's
`κ₁(n, τ)/δ` and `(κ₂(n, τ)/δ) log t` become `R κ(n, τ)/δ` and `R κ(n, τ)(1 + log t)/δ`. -/
theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ a b : ℕ,
      ∀ (n d : ℕ) (I : Instance n d) (B : Finset (Fin d)) (σ : Fin d → List (Fin n)),
        IsCyclicOrder I σ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T τ : ℕ) (ε₀ δ : ℝ) (Arr : ℕ → Ω → Fin n) (lam : ℕ → Ω → Fin n → ℝ)
        (lamBar : Ω → Fin n → ℝ) (xStar : Ω → Fin d → ℝ) (lamHat : ℕ → Ω → Fin n → ℝ)
        (c : Fin n → ℝ),
        IsSetting I B P T τ ε₀ δ Arr lam lamBar xStar lamHat c →
      ∀ (pick : ℕ → State n d → Fin n → Fin d), IsArgminRule I B σ pick →
      ∀ R : ℝ, (∀ m ∈ B, I.r m ≤ R) →
      ∀ t : ℕ, 1 ≤ t → t ≤ T →
        ((∀ m ∈ B, ¬ ((∃ i ∈ I.conf m, I.kind i = Kind.onQ) ∧
              (∃ i ∈ I.conf m, I.kind i = Kind.onNQ))) →
            expectedRegret I P (fun i => c i * T) pick Arr t ≤
              R * (C * (1 + (n : ℝ)) ^ a * (1 + (τ : ℝ)) ^ b) / δ) ∧
          expectedRegret I P (fun i => c i * T) pick Arr t ≤
            R * (C * (1 + (n : ℝ)) ^ a * (1 + (τ : ℝ)) ^ b) * (1 + Real.log t) / δ := by sorry

end MultiwaySoS
