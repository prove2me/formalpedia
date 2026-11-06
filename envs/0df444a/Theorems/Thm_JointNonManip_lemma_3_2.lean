-- Prove2me | Theorems.Thm_JointNonManip_lemma_3_2
-- name    : JointNonManip.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:17.544041+00:00
-- url     : https://prove2.me/theorems/210b6ad8-dc34-41b8-89cc-10f6bf6e4935
-- title:
--   Lemma 3.2 — Algorithm 1 keeps every path average and every menu point within Euclidean distance $\sqrt{2/T}$ of $S_{\mathrm{NE}}(G_{\mathcal L})$
-- statement:
--   Let $G$ be a finite game with nonempty action sets and learner utilities in $[-1,1]$, and run Algorithm 1 (with any choice of the auxiliary-game equilibrium in each round). For every horizon $T\ge1$:
--
--   1. for every optimizer policy and every realized path $c^{(1)},\dots,c^{(T)}$ of optimizer actions,
--   $$
--   \operatorname{dist}\Big(\frac1T\sum_{t=1}^T k^{(t)},\ S_{\mathrm{NE}}(G_{\mathcal L})\Big)\le\sqrt{\frac2T};
--   $$
--   2. $\sup_{\mu\in\mathcal M_T(\mathcal A_{\mathcal L})}\operatorname{dist}(\mu,S_{\mathrm{NE}}(G_{\mathcal L}))\le\sqrt{2/T}$;
--   3. any asymptotic menu of the base algorithm is contained in $S_{\mathrm{NE}}(G_{\mathcal L})$.
--
--   Here $k^{(t)}=e_{c^{(t)}}\otimes q^{(t)}$ and $\operatorname{dist}$ is the Euclidean distance. This is the upper containment $\mathcal M(\mathcal A_{\mathcal L})\subseteq S_{\mathrm{NE}}(G_{\mathcal L})$ used in Theorem 3.3.
--
--   Differences from the source:
--   - reading: Algorithm 1, which computes 'a mixed Nash equilibrium' of G̃(t) in every round → alg1Profile S for every selector S of auxiliary-game equilibria; reason: the algorithm fixes no choice among equilibria; the lemma is stated for every choice
--   - encoding: dist(µ, S_NE) ≤ √(2/T) in the Euclidean distance → ∃ s ∈ S_NE with l2dist µ s ≤ √(2/T); reason: S_NE is compact, so the infimum is attained
--   - encoding: for every optimizer policy and every realized path; T rounds → for every path c : Fin T → A0, and 1 ≤ T; reason: the bound depends only on the realized path; with T = 0 there are no rounds
--   - encoding: any asymptotic menu of the base algorithm → any set M with MenuConvergesTo (alg1Profile S) M; reason: Definition 2.4: the limit of M_T in Hausdorff distance
--   - encoding: Hausdorff distance between subsets of ∆(A) → Metric.hausdorffEDist for the sup metric of A → ℝ (MenuConvergesTo); reason: all norms on the finite-dimensional ℝ^A give the same Hausdorff convergence; hausdorffEDist is ⊤, not 0, against an empty set
--   - encoding: learners L = {1, …, n − 1}, finite action sets A₀, Aᵢ (a finite normal-form game, p.4) → a finite type L of learners (empty when n = 1) and finite nonempty types A0, Act i; reason: relabeling; ∆(Aᵢ) is empty unless Aᵢ is nonempty, so nonemptiness is part of the source's model
--   - encoding: CSPs µ ∈ ∆(A) ⊂ ℝ^A, y ⊗ q, ⟨·,·⟩, q = ⊗ᵢ xᵢ ∈ ∆(A_L), ℓ₁ and ℓ₂ norms → real functions on A0 × ((i : L) → Act i); otimes, pairing; AGT.profileProb x of a profile of lotteries AGT.IsLottery; explicit sums l1dist, l2dist; reason: Lean representation of the same objects
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), Lemma 3.2, p.9

import Mathlib
import Definitions.Def_JointNonManip_Algorithm1

namespace JointNonManip

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Lemma 3.2: Algorithm 1 approaches `S_NE` at rate `√(2/T)`** (Collina, Fullerton, Liu &
Weinberg, *Non-manipulability and Approachability Beyond Two-Player Games*, manuscript (STOC
2027 submission), Lemma 3.2, p.9).

For a finite game with nonempty action sets and learner utilities in `[−1, 1]`, and for every
way `S` of selecting the auxiliary-game equilibrium in Algorithm 1:
1. for every horizon `T ≥ 1` and every realized path `c` of optimizer actions,
   `dist((1/T) ∑ₜ k(t), S_NE(G_L)) ≤ √(2/T)` in the Euclidean distance;
2. every point of the horizon-`T` menu is within Euclidean distance `√(2/T)` of `S_NE(G_L)`;
3. every Hausdorff limit of the menus (asymptotic menu) is contained in `S_NE(G_L)`.

**Formalization Note** `dist(μ, S) ≤ r` is written `∃ s ∈ S, ‖μ − s‖₂ ≤ r`; `S_NE` is compact,
so this is the same condition. -/
theorem lemma_3_2 [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1) (S : AuxNESelector u) :
    (∀ T : ℕ, 1 ≤ T → ∀ c : Fin T → A0,
      ∃ s ∈ SNE u, l2dist (pathCSP (alg1Profile S) T c) s ≤ Real.sqrt (2 / T)) ∧
    (∀ T : ℕ, 1 ≤ T → ∀ μ ∈ menu (alg1Profile S) T,
      ∃ s ∈ SNE u, l2dist μ s ≤ Real.sqrt (2 / T)) ∧
    (∀ M : Set (A0 × ((i : L) → Act i) → ℝ),
      MenuConvergesTo (alg1Profile S) M → M ⊆ SNE u) := by sorry

end JointNonManip
