-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_15
-- name    : MultiwaySoS.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:40.154554+00:00
-- url     : https://prove2.me/theorems/3ea2fad0-2023-4485-bb7f-f315474ba77d
-- title:
--   Lemma 15 (Lipschitz Cost Lemma) — costs at two states differ by at most $8N$ when the queues differ by at most $N$
-- statement:
--   Let $m$ be a configuration with cyclic order $\sigma_m$, $i\in\mathcal I(m)$, and let $\mathscr Q,\tilde{\mathscr Q}$ be two arrays of virtual queues with $|\mathscr Q_{jm}-\tilde{\mathscr Q}_{jm}|\le N$ for every $j\in\mathcal I(m)$. Then
--   $$\big|\Delta\Phi_m(\tilde{\mathscr Q}_m,i)-\Delta\Phi_m(\mathscr Q_m,i)\big|\le8N .$$
--   With $\mathscr Q=\mathscr Q^s$, $\tilde{\mathscr Q}=\mathscr Q^t$ and $N=|s-t|$ this is the printed Lemma 15, since one step of any matching algorithm changes each virtual queue length by at most one.
--
--   Differences from the source:
--   - generalization: two states $\mathscr Q^s,\mathscr Q^t$ of a run at times $s,t$, bound $8|s-t|$ → two arbitrary arrays whose entries on $\mathcal I(m)$ differ by at most $N$, bound $8N$; reason: one commitment changes each entry by at most $1$, so states at times $s,t$ differ by at most $|s-t|$; the statement specializes to the printed one
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 15, p.40

import Mathlib
import Definitions.Def_MultiwaySoS_Algorithm

namespace MultiwaySoS

/-- Lemma 15, Lipschitz Cost Lemma (arXiv:2112.04622v3, p.40), in the form of two states at
distance `N` (the printed form is `N = |s − t|`, since one step of any matching algorithm changes
each virtual queue length by at most one).

For a configuration `m`, a type `i ∈ I(m)`, and two virtual states `𝒬`, `𝒬̃` with
`|𝒬_jm − 𝒬̃_jm| ≤ N` for every `j ∈ I(m)`:
`|(Φ_m(𝒬̃'_m) − Φ_m(𝒬̃_m)) − (Φ_m(𝒬'_m) − Φ_m(𝒬_m))| ≤ 8N`, where `'` denotes the state after
committing `i` to `m`. -/
theorem lemma_15 {n d : ℕ} (I : Instance n d) (σ : Fin d → List (Fin n))
    (hσ : IsCyclicOrder I σ) (m : Fin d) (i : Fin n) (hi : i ∈ I.conf m) (q q' : Fin n → ℤ)
    (N : ℕ) (hN : ∀ j ∈ I.conf m, |q j - q' j| ≤ N) :
    |deltaPhi I (σ m) m q' i - deltaPhi I (σ m) m q i| ≤ 8 * N := by sorry

end MultiwaySoS
