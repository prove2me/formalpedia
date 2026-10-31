-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_7
-- name    : MultiwaySoS.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:56.85958+00:00
-- url     : https://prove2.me/theorems/a44dbbaf-f833-4e89-a8b7-43c6cf5aa58a
-- title:
--   Lemma 7 (without the $O(\tau)$ term) — $\mathbb E[\mathrm{OPT}(A^t)]-\mathbb E[\sum_mr_m\mathscr X^t_m]\le\alpha^*\cdot\sum_{m}\mathbb E[\mathscr Q^t_m]$
-- statement:
--   Under the hypotheses of Theorem 2 (the arrival model, Assumption 1 with basis $\mathcal M_+$, smoothed GPG$_{\delta,\tau}$ with $\delta>0$), run Algorithm 2 with an arg-min commit rule, and let $\alpha=r^\top_{\mathcal M_+}M^{-1}_{\mathcal M_+}$ (the solution of $\alpha\cdot M_m=r_m$, $m\in\mathcal M_+$). For every $t\in[1,T]$,
--   $$\mathbb E[\mathrm{OPT}(A^t)]-\mathbb E\Big[\sum_mr_m\mathscr X^t_m\Big]\le\alpha\cdot\sum_{m\in\mathcal M_+}\mathbb E[\mathscr Q^t_m].$$
--
--   This turns the sample-path Lemma 6 into the expected bound used in the proof of Theorem 2.
--
--   Differences from the source:
--   - generalization: right side $r^\top_{\mathcal M_+}M^{-1}_{\mathcal M_+}\sum_m\mathbb E[\mathscr Q^t_m]+O(\tau)$ → the same without the $O(\tau)$ term; reason: weak duality gives $\mathrm{OPT}(v)\le\alpha\cdot v$ for all $v\ge0$, so no error term is needed; the statement implies the printed one and avoids an unquantified $O(\cdot)$
--   - reading: "the distribution $\lambda^t$ from which the type $I^t$ is sampled is itself a random quantity, which is $\mathcal F^{t-1}$-measurable. Conditioned on the sequence $\{\lambda^t\}$, $\{I^t\}$ are assumed to be mutually independent" (p.15) → $P(I^t=i\mid\mathcal F^{t-1})=\lambda^t_i$, written as $P(A\cap\{I^t=i\})=\int_A\lambda^t_i\,dP$ for $A\in\mathcal F^{t-1}$; reason: this is the sampling sentence of the page; the conditional-independence sentence is not assumed separately, because it would add no constraint the proof uses once each $I^t$ is drawn from the predictable $\lambda^t$
--   - reading: Assumption 1: "almost surely $\bar\lambda$ satisfies GPG$_{\epsilon_0}$"; "we fix an optimal basic feasible solution $x^*$ and its basis $\mathcal M_+$" (p.16) → $\bar\lambda$ and $x^*$ are random, the basis $\mathcal M_+$ is one fixed set, GPG holds almost surely; Assumption 2 and the offline requirement hold almost surely; reason: Algorithm 2 needs a fixed $\mathcal M_+$; a deterministic $\bar\lambda$ is the constant case, so this reading is the stronger statement
--   - generalization: $0<\delta<\epsilon_0$ (Assumption 2, Theorem 2) → $0<\delta\le\epsilon_0$; reason: p.17 (example 2) and p.18 use $\delta=\epsilon_0$; the range contains the printed one
--   - reading: $m^t=\arg\min_m\{\Delta\Phi_m(\mathscr Q^{t-1}_m,I^t)\}$ with no tie-breaking rule → every commit rule that returns a minimizer, possibly depending on the time and the whole state; reason: ties are arbitrary in the paper; a statement for every such rule covers each of them
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
--   - reading: second line of (10): $Q_{i^\prime m}+\mathbb 1\{i^\prime=i\}<M_{im}$ → $Q_{i^\prime m}+\mathbb 1\{i^\prime=i\}<M_{i^\prime m}$; reason: obvious intent; both entries equal $1$ for $i,i^\prime\in\mathcal I(m)$
--   - encoding: types $[n]$ split into the intervals $\mathcal I^{\rm off},\mathcal I^{\rm on\text{-}q},\mathcal I^{\rm on\text{-}nq}$; configurations $\mathcal M$ → `Fin n` with a labelling `kind`, configurations `Fin d`, time $1$-based, queue lengths in $\mathbb Z$; reason: a renumbering of the types; same instances
--   - reading: Definition 2 (GPG), clause 2 "with $\mathcal M_+$ as the basic activities", and clause 1 → the support of the solution is exactly $\mathcal M_+$, whose columns are linearly independent; clause 1 is not written; reason: basic activities are the non-zero components (p.4); clause 1 follows from linear independence
--   - encoding: $\mathrm{OPT}(A^t)$, the optimal value of the LP → `sSup` of the objective over the feasible set; reason: for $A^t\ge0$ the set is nonempty (discard singletons) and bounded above under GPG (weak duality), so the supremum is the LP value
--   - encoding: $r^\top_{\mathcal M_+}M^{-1}_{\mathcal M_+}$ → any $\alpha$ with $\alpha\cdot M_m=r_m$ for $m\in\mathcal M_+$; reason: under GPG this $\alpha$ exists and is unique (basis facts), so the two are the same vector
--   - encoding: $\sum_{s=1}^{t-2\tau}\hat\lambda^s$ in Assumption 2 → `Finset.Icc 1 (t - 2 * τ)` with truncated subtraction; reason: the sum is empty for $t\le2\tau$, the paper's meaning; no instance changes
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 7, p.23

import Mathlib
import Definitions.Def_MultiwaySoS_Setting

open MeasureTheory

namespace MultiwaySoS

/-- Lemma 7 (arXiv:2112.04622v3, p.23), without the `O(τ)` term.

Under the hypotheses of Theorem 2 (`IsSetting`: Assumption 1, the arrival model, Smoothed
`GPG_{δ,τ}`), for Algorithm 2 with an arg-min commit rule, every `t ∈ [1, T]` and
`α = r^⊤_{M₊} M^{−1}_{M₊}` (the solution of `α·M_m = r_m`, `m ∈ M₊`):
`E[OPT(A^t)] − E[∑_m r_m 𝒳^t_m] ≤ α·∑_{m ∈ M₊} E[𝒬^t_m]`.

The printed statement has `+ O(τ)` on the right; the statement without it implies the printed one. -/
theorem lemma_7 {n d : ℕ} (I : Instance n d) (B : Finset (Fin d)) (σ : Fin d → List (Fin n))
    (hσ : IsCyclicOrder I σ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T τ : ℕ) (ε₀ δ : ℝ) (Arr : ℕ → Ω → Fin n)
    (lam : ℕ → Ω → Fin n → ℝ) (lamBar : Ω → Fin n → ℝ) (xStar : Ω → Fin d → ℝ)
    (lamHat : ℕ → Ω → Fin n → ℝ) (c : Fin n → ℝ)
    (hS : IsSetting I B P T τ ε₀ δ Arr lam lamBar xStar lamHat c)
    (pick : ℕ → State n d → Fin n → Fin d) (hpick : IsArgminRule I B σ pick)
    (α : Fin n → ℝ) (hα : ∀ m ∈ B, ∑ i, I.M i m * α i = I.r m) (t : ℕ) (ht1 : 1 ≤ t)
    (htT : t ≤ T) :
    (∫ ω, OPT I (arrCount (fun s => Arr s ω) t) ∂P) -
        ∫ ω, virtualReward I (fun i => c i * T) pick (fun s => Arr s ω) t ∂P ≤
      ∑ i, α i * ∑ m ∈ B,
        ∫ ω, ((run I (fun i => c i * T) pick (fun s => Arr s ω) t).Qv I i m : ℝ) ∂P := by sorry

end MultiwaySoS
