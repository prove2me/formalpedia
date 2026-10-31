-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_5
-- name    : MultiwaySoS.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:34.651335+00:00
-- url     : https://prove2.me/theorems/8dea7652-3856-4d4c-b3fd-ebe0eeeb8b85
-- title:
--   Lemma 5 — the gap $\mathscr X^t_m-X^t_m$ between virtual and true matches
-- statement:
--   Run Algorithm 2 with an arg-min commit rule on an arrival sequence in which every offline type $i$ arrives $A^T_i=c_iT$ times, with offline inventories $\bar\lambda_iT=c_iT$, and let every type lie in some configuration of $\mathcal M_+$. Write $(x)^-=\max\{-x,0\}$. For every $t\le T$ and $m\in\mathcal M_+$:
--
--   **Case 1** ($\mathcal I(m)\cap\mathcal I^{\rm on\text{-}q}\neq\emptyset$ and $\mathcal I(m)\cap\mathcal I^{\rm on\text{-}nq}\neq\emptyset$):
--   $$\mathscr X^t_m-X^t_m\le\max_{i\in\mathcal I(m)\cap\mathcal I^{\rm on\text{-}q}}\max_{s\in[t]}(\mathscr Q^s_{im})^-+\sum_{i\in\mathcal I(m)\cap\mathcal I^{\rm off}}\ \sum_{m^\prime\in\mathcal M_+:\,i\in\mathcal I(m^\prime)}(\mathscr Q^t_{im^\prime})^-+|\mathcal I(m)| .$$
--
--   **Case 2** (otherwise):
--   $$\mathscr X^t_m-X^t_m\le\sum_{i\in\mathcal I(m)\cap\mathcal I^{\rm off}}\ \sum_{m^\prime\in\mathcal M_+:\,i\in\mathcal I(m^\prime)}(\mathscr Q^t_{im^\prime})^-+|\mathcal I(m)| .$$
--
--   This is Step 1 of the proof of Theorem 2: the true reward differs from the virtual reward by negative parts of virtual queues.
--
--   Differences from the source:
--   - generalization: a run of Algorithm 2 under the hypotheses of Theorem 2 (GPG) → any arrival sequence and any basis $\mathcal M_+$ such that every type lies in some configuration of $\mathcal M_+$; reason: GPG implies this covering property (the optimal solutions with support $\mathcal M_+$ reproduce every distribution of the ball); the statement specializes to the paper\'s runs
--   - reading: $m^t=\arg\min_m\{\Delta\Phi_m(\mathscr Q^{t-1}_m,I^t)\}$ with no tie-breaking rule → every commit rule that returns a minimizer, possibly depending on the time and the whole state; reason: ties are arbitrary in the paper; a statement for every such rule covers each of them
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
--   - reading: second line of (10): $Q_{i^\prime m}+\mathbb 1\{i^\prime=i\}<M_{im}$ → $Q_{i^\prime m}+\mathbb 1\{i^\prime=i\}<M_{i^\prime m}$; reason: obvious intent; both entries equal $1$ for $i,i^\prime\in\mathcal I(m)$
--   - encoding: types $[n]$ split into the intervals $\mathcal I^{\rm off},\mathcal I^{\rm on\text{-}q},\mathcal I^{\rm on\text{-}nq}$; configurations $\mathcal M$ → `Fin n` with a labelling `kind`, configurations `Fin d`, time $1$-based, queue lengths in $\mathbb Z$; reason: a renumbering of the types; same instances
--   - encoding: $\sum_{m^\prime:\,i\in\mathcal I(m^\prime)}$ → the sum over $m^\prime\in\mathcal M_+$ with $i\in\mathcal I(m^\prime)$; reason: only configurations of $\mathcal M_+$ have virtual queues; the others have $\mathscr Q=Y=0$
--   - reading: "$A^T_i=\bar\lambda_i\cdot T$ with probability 1" for offline $i$ (p.15) → a pathwise hypothesis $A^T_i=c_iT$ on the arrival sequence, with $t\le T$; reason: Lemma 5 is a sample-path statement; the almost-sure version follows
--   - reading: "For a configuration $m$" → $m\in\mathcal M_+$; reason: $Y$, $\mathscr X$ and the queues exist only for configurations of $\mathcal M_+$ (p.19, Algorithm 2)
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 5, p.22

import Mathlib
import Definitions.Def_MultiwaySoS_Algorithm

namespace MultiwaySoS

/-- Lemma 5 (arXiv:2112.04622v3, p.22): the gap between virtual and true matches.

Run Algorithm 2 with an arg-min commit rule on an arrival sequence for which every offline type
`i` has `A^T_i = c_i T` arrivals, with offline inventories `λ̄_i T = c_i T`, and let `t ≤ T`,
`m ∈ M₊`. Write `(x)⁻ = max{−x, 0}`. Then

* Case 1 (`I(m) ∩ I^on-q ≠ ∅` and `I(m) ∩ I^on-nq ≠ ∅`):
  `𝒳^t_m − X^t_m ≤ max_{i ∈ I(m) ∩ I^on-q} max_{s ∈ [t]} (𝒬^s_im)⁻
    + ∑_{i ∈ I(m) ∩ I^off} ∑_{m' ∈ M₊ : i ∈ I(m')} (𝒬^t_im')⁻ + |I(m)|`;
* Case 2 (otherwise):
  `𝒳^t_m − X^t_m ≤ ∑_{i ∈ I(m) ∩ I^off} ∑_{m' ∈ M₊ : i ∈ I(m')} (𝒬^t_im')⁻ + |I(m)|`.

**Formalization Note.** The double maximum over the finite set `[t] × (I(m) ∩ I^on-q)` is a
`Finset.sup` of natural numbers (empty maximum `0`). The inner sums run over `m' ∈ M₊`, the only
configurations with virtual queues. -/
theorem lemma_5 {n d : ℕ} (I : Instance n d) (B : Finset (Fin d)) (σ : Fin d → List (Fin n))
    (hσ : IsCyclicOrder I σ) (c : Fin n → ℝ) (T : ℕ) (pick : ℕ → State n d → Fin n → Fin d)
    (hpick : IsArgminRule I B σ pick) (hcover : ∀ i, ∃ m ∈ B, i ∈ I.conf m) (arr : ℕ → Fin n)
    (hoff : ∀ i, I.kind i = Kind.off → arrCount arr T i = c i * T) (t : ℕ) (ht : t ≤ T)
    (m : Fin d) (hm : m ∈ B) :
    let s : ℕ → State n d := fun u => run I (fun i => c i * T) pick arr u
    let neg : ℤ → ℤ := fun x => max (-x) 0
    let offTerm : ℤ := ∑ i ∈ (I.conf m).filter (fun i => I.kind i = Kind.off),
      ∑ m' ∈ B.filter (fun m' => i ∈ I.conf m'), neg ((s t).Qv I i m')
    let mixed : Prop := (∃ i ∈ I.conf m, I.kind i = Kind.onQ) ∧ (∃ i ∈ I.conf m, I.kind i = Kind.onNQ)
    (mixed → ((s t).Xv m : ℤ) - ((s t).X m : ℤ) ≤
        ((((Finset.Icc 1 t) ×ˢ ((I.conf m).filter (fun i => I.kind i = Kind.onQ))).sup
          (fun p => (neg ((s p.1).Qv I p.2 m)).toNat) : ℕ) : ℤ) + offTerm + (I.conf m).card) ∧
      (¬ mixed → ((s t).Xv m : ℤ) - ((s t).X m : ℤ) ≤ offTerm + (I.conf m).card) := by sorry

end MultiwaySoS
