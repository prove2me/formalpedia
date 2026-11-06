-- Prove2me | Theorems.Thm_JointNonManip_theorem_3_3
-- name    : JointNonManip.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:25.854192+00:00
-- url     : https://prove2.me/theorems/dc041b99-0461-4da5-818a-6254dc666350
-- title:
--   Theorem 3.3 — independent learners with no swap regret, joint non-manipulability and asymptotic menu $S_{\mathrm{NE}}(G_{\mathcal L})$ (corrected: menu equality needs $|A_0|\ge2$)
-- statement:
--   Let $G=(A_0,A_1,\dots,A_{n-1},u_0,\dots,u_{n-1})$ be a finite game with nonempty action sets and learner utilities $u_i:A\to[-1,1]$. There is a horizon-aware profile $\mathcal A'_{\mathcal L}$ of learner algorithms, computed from the learners' data $G_{\mathcal L}$ alone, in which every learner randomizes independently and its mixed strategy depends only on the optimizer's past actions, such that:
--
--   1. **no swap regret:** for every learner $i$, $\sup_{\pi_T}\mathbb E[R_i^{\mathrm{sw}}(T)]=o(T)$ over all adaptive optimizer policies $\pi_T$;
--   2. **joint non-manipulability:** for every optimizer utility $u_0:A\to[-1,1]$,
--   $$
--   \sup_{\pi_T}\langle u_0,\varphi_T(\pi_T,\mathcal A'_{\mathcal L})\rangle\le\sup_{y\in\Delta(A_0)}\langle u_0,\varphi_T(y^{\otimes T},\mathcal A'_{\mathcal L})\rangle+o(1);
--   $$
--   3. **menu:** if $|A_0|\ge2$, the horizon-$T$ menus converge in Hausdorff distance to $S_{\mathrm{NE}}(G_{\mathcal L})$, that is,
--   $$
--   \mathcal M(\mathcal A'_{\mathcal L})=S_{\mathrm{NE}}(G_{\mathcal L}).
--   $$
--
--   This is the paper's first main result: independent learners can keep the swap-regret guarantee of each learner while removing every incentive for the optimizer to adapt dynamically, and the set of outcomes the optimizer can induce is exactly the convex hull of the Nash-response outcomes.
--
--   **Formalization Note** The profile is chosen before the optimizer utility $u_0$, so it cannot depend on it. With a single optimizer action every menu is a single point, so the menu clause needs $|A_0|\ge2$; clauses 1 and 2 hold for every $A_0$.
--
--   Differences from the source:
--   - correction: M(A'_L) = S_NE(G_L), with no hypothesis on A₀ → 2 ≤ Fintype.card A0 → MenuConvergesTo P (SNE u); reason: false for |A₀| = 1: A₀ = {c}, one learner with A₁ = {0, 1} and u₁ ≡ 0; S_NE is the segment between e_c ⊗ e₀ and e_c ⊗ e₁, while each M_T is a single point because there is one optimizer sequence (checked in Lean: Solutions/verification/JointNonManip_sanity.lean, not_menuConverges); the source's own Lemma A.4 (p.26) assumes |A₀| ≥ 2 and p.38 says menu equality 'is not asserted in this degenerate case'
--   - reading: the resulting algorithms' asymptotic menu M(A'_L) = S_NE(G_L) → also clauses 1 (no swap regret) and 2 (joint non-manipulability), for every A₀; reason: the Introduction (p.2) attributes 'vanishing regret and jointly non-manipulable (Theorem 3.3)' to it, and its proof cites Lemma 3.1, whose conclusion these are; p.38 keeps both for |A₀| = 1
--   - reading: we can modify Algorithm 1 so that the resulting algorithms … → there exists a profile P of learner algorithms such that …; reason: 'modify Algorithm 1' constrains how the profile is built, not what it is; the modification of Lemma A.4 is one such profile
--   - reading: a profile of learner algorithms A_L → a horizon-aware profile (indexed by the horizon T); reason: the profile of Theorem 3.3 is the horizon-aware augmentation of Lemma A.4 (p.26; p.38 'The construction is horizon-aware'), and Lemma 3.1 is applied to it; horizon-independent profiles are the special case constant in T
--   - encoding: learner algorithms whose mixed strategies are determined by the optimizer's past actions; optimizer policies choosing y(t) adaptively from the history and the current q(t); φ_T and E[R^sw_i(T)] as expectations → Profile (lotteries x T t (c(1..t)) i); Policy (lotteries y(t) as functions of the past optimizer and learner actions); expectations as finite sums over trajectories weighted by trajWeight; reason: the model of p.4: q(t) is a function of the history and the fixed profile, so it is not a separate argument of the policy
--   - encoding: o(T) and o(1) uniformly over optimizer policies; sup_π ⟨u₀, φ_T(π)⟩ ≤ sup_y ⟨u₀, φ_T(y^{⊗T})⟩ + o(1); inf_y ‖·‖₁ = o(1) → ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ∀ π (NoSwapRegret, JointlyNonManipulable: every π is matched within ε by a static y); ∃ y within ε; reason: the definition of o(·); a supremum (infimum) is at most (at least) a bound up to ε iff every element is (some element is) within ε
--   - encoding: Hausdorff distance between subsets of ∆(A) → Metric.hausdorffEDist for the sup metric of A → ℝ (MenuConvergesTo); reason: all norms on the finite-dimensional ℝ^A give the same Hausdorff convergence; hausdorffEDist is ⊤, not 0, against an empty set
--   - encoding: learners L = {1, …, n − 1}, finite action sets A₀, Aᵢ (a finite normal-form game, p.4) → a finite type L of learners (empty when n = 1) and finite nonempty types A0, Act i; reason: relabeling; ∆(Aᵢ) is empty unless Aᵢ is nonempty, so nonemptiness is part of the source's model
--   - encoding: CSPs µ ∈ ∆(A) ⊂ ℝ^A, y ⊗ q, ⟨·,·⟩, q = ⊗ᵢ xᵢ ∈ ∆(A_L), ℓ₁ and ℓ₂ norms → real functions on A0 × ((i : L) → Act i); otimes, pairing; AGT.profileProb x of a profile of lotteries AGT.IsLottery; explicit sums l1dist, l2dist; reason: Lean representation of the same objects
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), Theorem 3.3, p.10; with Lemma 3.1, p.7, Lemma A.4, p.26, the Introduction, p.2, and p.38

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

namespace JointNonManip

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Theorem 3.3: independent learners with no swap regret, joint non-manipulability and
asymptotic menu `S_NE(G_L)`** (Collina, Fullerton, Liu & Weinberg, *Non-manipulability and
Approachability Beyond Two-Player Games*, manuscript (STOC 2027 submission), Theorem 3.3, p.10,
with the guarantees of Lemma 3.1, p.7, used in its proof and stated in the Introduction, p.2).

For every finite game with nonempty action sets and learner utilities in `[−1, 1]`, there is a
horizon-aware profile `P` of independent learner algorithms whose mixed strategies depend only on
the learners' data `G_L` and the optimizer's past actions, such that
1. every learner has no swap regret against every adaptive optimizer;
2. the profile is jointly non-manipulable, for every optimizer utility `u₀ : A → [−1, 1]`;
3. if `|A₀| ≥ 2`, the horizon-`T` menus converge to `S_NE(G_L)` in Hausdorff distance, i.e.
   `M(A'_L) = S_NE(G_L)`.

**Formalization Note** The menu clause carries the hypothesis `|A₀| ≥ 2` of Lemma A.4 (p.26):
with a single optimizer action every menu is a singleton, while `S_NE` need not be (p.38:
"Full menu equality with SNE is not asserted in this degenerate case"). Clauses 1 and 2 hold
without it. -/
theorem theorem_3_3 [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1) :
    ∃ P : Profile A0 Act,
      NoSwapRegret u P ∧ JointlyNonManipulable P ∧
        (2 ≤ Fintype.card A0 → MenuConvergesTo P (SNE u)) := by sorry

end JointNonManip
