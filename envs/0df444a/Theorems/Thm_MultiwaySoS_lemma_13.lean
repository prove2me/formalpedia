-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_13
-- name    : MultiwaySoS.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:44.754114+00:00
-- url     : https://prove2.me/theorems/4cdd29f1-170d-4adb-a5e5-f08106d899a2
-- title:
--   Lemma 13 — a type $i^*$ whose SS packing decreases $\Phi$ by $2\sqrt{\Phi}/B$ when $\Phi\ge B^2$, $B=2n^2$
-- statement:
--   Let $n\ge1$, let $\mathcal M_+$ have at most $n$ configurations, and set $B=2n^2$. For every array of virtual queues $\mathscr Q$ with $\Phi(\mathscr Q)\ge B^2$ there is a resource type $i^*$ and a configuration $m\in\mathcal M_+$ containing $i^*$ with
--   $$\Delta\Phi_m(\mathscr Q_m,i^*)\le-\frac{2\sqrt{\Phi(\mathscr Q)}}{B}.$$
--   Since SS commits $i^*$ to a configuration minimizing $\Delta\Phi_m(\mathscr Q_m,i^*)$, packing an item of type $i^*$ by SS changes the potential by at most $-2\sqrt{\Phi(\mathscr Q)}/B$.
--
--   Differences from the source:
--   - generalization: a state encountered during the execution of SS under GPG → any integer array $\mathscr Q$, with $n\ge1$ and $|\mathcal M_+|\le n$; reason: the proof uses only $|\mathcal M_+|=n$ (a consequence of GPG, p.46) and no property of reachable states
--   - encoding: "if an item of type $i^*$ is packed by SS, $\Phi(\mathscr Q^\prime)-\Phi(\mathscr Q)\le\dots$" → some $m\in\mathcal M_+$ containing $i^*$ has $\Delta\Phi_m\le\dots$; reason: SS takes the minimum of $\Delta\Phi_m$ over these $m$, so the two statements are equivalent
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 13, p.39

import Mathlib
import Definitions.Def_MultiwaySoS_Algorithm

namespace MultiwaySoS

/-- Lemma 13 (arXiv:2112.04622v3, p.39).

Let `Bc := 2n²`. For every state `𝒬` with `Φ(𝒬) ≥ Bc²` there is a resource type `i*` such that
packing an item of type `i*` by SS changes the potential by at most `−2√Φ(𝒬)/Bc`: some
configuration `m ∈ M₊` containing `i*` has `ΔΦ_m(𝒬_m, i*) ≤ −2√Φ(𝒬)/Bc` (SS takes the minimum of
`ΔΦ_m(𝒬_m, i*)` over these `m`).

**Formalization Note.** The lemma is stated for every array `𝒬`, not only for states reached by
SS, under `n ≥ 1` and `|M₊| ≤ n`, the two facts about `M₊` its proof uses (both follow from GPG,
where `|M₊| = n`). -/
theorem lemma_13 {n d : ℕ} (I : Instance n d) (B : Finset (Fin d)) (σ : Fin d → List (Fin n))
    (hσ : IsCyclicOrder I σ) (hn : 0 < n) (hB : B.card ≤ n) (Q : Fin n → Fin d → ℤ)
    (hΦ : (2 * (n : ℝ) ^ 2) ^ 2 ≤ ((Phi B σ Q : ℤ) : ℝ)) :
    ∃ i, ∃ m ∈ B, i ∈ I.conf m ∧
      ((deltaPhi I (σ m) m (fun j => Q j m) i : ℤ) : ℝ) ≤
        -2 * Real.sqrt ((Phi B σ Q : ℤ) : ℝ) / (2 * (n : ℝ) ^ 2) := by sorry

end MultiwaySoS
