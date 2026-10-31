-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_10
-- name    : MultiwaySoS.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:41.260688+00:00
-- url     : https://prove2.me/theorems/a68649dd-ae60-466f-9674-b668321d67cf
-- title:
--   Lemma 10 (corrected: cost $0$ when $\ell_m=1$) — elementary cost $\Phi_m(\mathscr Q^\prime_m)-\Phi_m(\mathscr Q_m)=2(\delta_i-\delta_{i+1})+2$
-- statement:
--   Let $m\in\mathcal M_+$ with cyclic order $\sigma_m=(a_0,\dots,a_{\ell-1})$, let $\mathscr Q$ be any array of virtual queue lengths, and set $\delta_j=\mathscr Q_{a_jm}-\mathscr Q_{a_{j-1}m}$ (indices modulo $\ell$). Commit one unit of type $a_k$ to $m$ (with a virtual match when virtual\_feasible holds), and let $\mathrm{cost}=\Phi_m(\mathscr Q^\prime_m)-\Phi_m(\mathscr Q_m)$. Then
--
--   1. if $\ell\ge2$: $\mathrm{cost}=2(\delta_k-\delta_{k+1})+2$;
--   2. if $\ell=1$: $\mathrm{cost}=0$;
--   3. in all cases
--   $$|\mathrm{cost}|\le\sqrt{8\Phi(\mathscr Q)}+2 .$$
--
--   The differences $\delta_j$ are cyclic differences of queue lengths, unrelated to the gap parameter $\delta$.
--
--   Differences from the source:
--   - correction: $\mathrm{cost}=2(\delta_i-\delta_{i+1})+2$ for every configuration → this formula for $\ell_m\ge2$, and $\mathrm{cost}=0$ for $\ell_m=1$; reason: for a singleton configuration $\Phi_m\equiv0$, so the cost is $0$, while $\delta_1=\delta_2=0$ gives $2$; singletons occur in $\mathcal M_+$ (the discard configuration $\{1\}$ of the instance with $a=\{1,2\}$, $b=\{1\}$, $\bar\lambda=(2/3,1/3)$)
--   - generalization: the state of the queues of Algorithm 2 → any integer array $\mathscr Q$; reason: the proof uses no property of reachable states
--   - encoding: $\mathcal I(m)=[\ell]$, $\sigma_m=(1,\dots,\ell)$, $1$-based indices → the list $\sigma_m=(a_0,\dots,a_{\ell-1})$, $0$-based indices modulo $\ell$; reason: the paper\'s "without loss of generality" relabelling
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
--   - reading: "a configuration $m$" → $m\in\mathcal M_+$; reason: virtual queues exist only for configurations of $\mathcal M_+$ (p.19), and $\Phi$ sums over $\mathcal M_+$, so the bound by $\Phi$ has no content for another $m$
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 10, p.39

import Mathlib
import Definitions.Def_MultiwaySoS_Algorithm

namespace MultiwaySoS

/-- Lemma 10, Elementary Cost Functions (arXiv:2112.04622v3, p.39), corrected for `ℓ_m = 1`.

Let `m ∈ M₊`, `σ_m = (a_0, …, a_{ℓ−1})` its cyclic order, `𝒬` any array of virtual queue lengths,
and `δ_j = 𝒬_{a_j m} − 𝒬_{a_{j−1} m}` (indices mod `ℓ`). Committing one unit of type `a_k` to `m`
(with a virtual match when `virtual_feasible` holds) changes `Φ_m` by
`cost = Φ_m(𝒬'_m) − Φ_m(𝒬_m)`, and
1. `cost = 2(δ_k − δ_{k+1}) + 2` if `ℓ ≥ 2`;
2. `cost = 0` if `ℓ = 1`;
3. `|cost| ≤ √(8Φ(𝒬)) + 2`.

**Formalization Note.** Indices are 0-based, `δ_k` is `δc k` and `δ_{k+1}` is `δc (k+1)`, with
`j mod ℓ`. The paper's `δ_i` (cyclic differences) are unrelated to the gap parameter `δ`. -/
theorem lemma_10 {n d : ℕ} (I : Instance n d) (B : Finset (Fin d)) (σ : Fin d → List (Fin n))
    (hσ : IsCyclicOrder I σ) (m : Fin d) (hm : m ∈ B) (Q : Fin n → Fin d → ℤ)
    (k : Fin (σ m).length) :
    let ℓ := (σ m).length
    let q : Fin n → ℤ := fun j => Q j m
    let δc : ℕ → ℤ := fun j =>
      q ((σ m).get ⟨j % ℓ, Nat.mod_lt _ (Fin.pos k)⟩) -
        q ((σ m).get ⟨(j + ℓ - 1) % ℓ, Nat.mod_lt _ (Fin.pos k)⟩)
    let cost : ℤ := deltaPhi I (σ m) m q ((σ m).get k)
    (2 ≤ ℓ → cost = 2 * (δc k - δc (k + 1)) + 2) ∧ (ℓ = 1 → cost = 0) ∧
      |(cost : ℝ)| ≤ Real.sqrt (8 * ((Phi B σ Q : ℤ) : ℝ)) + 2 := by sorry

end MultiwaySoS
