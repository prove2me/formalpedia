-- Prove2me | Theorems.Thm_JointNonManip_lemma_3_1
-- name    : JointNonManip.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:07.485924+00:00
-- url     : https://prove2.me/theorems/81dad6de-2fb9-4603-b5d8-1673e0db570f
-- title:
--   Lemma 3.1 — the menu criterion: swap inequalities on $\mathcal M$ and statically attainable product extreme points give no swap regret and joint non-manipulability
-- statement:
--   Fix a finite game with nonempty action sets and utilities in $[-1,1]$, and a profile $\mathcal A_{\mathcal L}$ of learner algorithms whose horizon-$T$ menus converge in Hausdorff distance to the asymptotic menu $\mathcal M=\mathcal M(\mathcal A_{\mathcal L})$. Suppose:
--
--   1. every $\mu\in\mathcal M$ has $G_{i,\phi}(\mu)\le 0$ for every learner $i$ and every swap $\phi:A_i\to A_i$;
--   2. every extreme point $s$ of $\mathcal M$ is a product distribution $s=y_s\otimes q_s$, and is asymptotically attainable by a static optimizer strategy:
--   $$
--   \inf_{y\in\Delta(A_0)}\big\|\varphi_T(y^{\otimes T},\mathcal A_{\mathcal L})-s\big\|_1=o(1).
--   $$
--
--   Then every learner has no swap regret (expected swap regret $o(T)$ uniformly over adaptive optimizer policies), and the profile is jointly non-manipulable.
--
--   The lemma reduces the two strategic guarantees to two geometric properties of the menu; Theorem 3.3 applies it to the menu $S_{\mathrm{NE}}(G_{\mathcal L})$.
--
--   **Formalization Note** The asymptotic menu is a closed set $\mathcal M$ to which the menus converge; the $o(1)$ in hypothesis 2 is for each extreme point separately.
--
--   Differences from the source:
--   - encoding: the asymptotic menu M = M(A_L), the Hausdorff limit of M_T(A_L) → any closed set M with MenuConvergesTo P M; reason: a Hausdorff limit is determined only up to closure, and the proof uses 'the compact convex set M' (p.26)
--   - reading: a profile of learner algorithms A_L → a horizon-aware profile (indexed by the horizon T); reason: the profile of Theorem 3.3 is the horizon-aware augmentation of Lemma A.4 (p.26; p.38 'The construction is horizon-aware'), and Lemma 3.1 is applied to it; horizon-independent profiles are the special case constant in T
--   - encoding: learner algorithms whose mixed strategies are determined by the optimizer's past actions; optimizer policies choosing y(t) adaptively from the history and the current q(t); φ_T and E[R^sw_i(T)] as expectations → Profile (lotteries x T t (c(1..t)) i); Policy (lotteries y(t) as functions of the past optimizer and learner actions); expectations as finite sums over trajectories weighted by trajWeight; reason: the model of p.4: q(t) is a function of the history and the fixed profile, so it is not a separate argument of the policy
--   - encoding: o(T) and o(1) uniformly over optimizer policies; sup_π ⟨u₀, φ_T(π)⟩ ≤ sup_y ⟨u₀, φ_T(y^{⊗T})⟩ + o(1); inf_y ‖·‖₁ = o(1) → ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ∀ π (NoSwapRegret, JointlyNonManipulable: every π is matched within ε by a static y); ∃ y within ε; reason: the definition of o(·); a supremum (infimum) is at most (at least) a bound up to ε iff every element is (some element is) within ε
--   - encoding: Hausdorff distance between subsets of ∆(A) → Metric.hausdorffEDist for the sup metric of A → ℝ (MenuConvergesTo); reason: all norms on the finite-dimensional ℝ^A give the same Hausdorff convergence; hausdorffEDist is ⊤, not 0, against an empty set
--   - encoding: learners L = {1, …, n − 1}, finite action sets A₀, Aᵢ (a finite normal-form game, p.4) → a finite type L of learners (empty when n = 1) and finite nonempty types A0, Act i; reason: relabeling; ∆(Aᵢ) is empty unless Aᵢ is nonempty, so nonemptiness is part of the source's model
--   - encoding: CSPs µ ∈ ∆(A) ⊂ ℝ^A, y ⊗ q, ⟨·,·⟩, q = ⊗ᵢ xᵢ ∈ ∆(A_L), ℓ₁ and ℓ₂ norms → real functions on A0 × ((i : L) → Act i); otimes, pairing; AGT.profileProb x of a profile of lotteries AGT.IsLottery; explicit sums l1dist, l2dist; reason: Lean representation of the same objects
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), Lemma 3.1, p.7; proof in App. A.5, p.26

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

namespace JointNonManip

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Lemma 3.1: the menu criterion for no swap regret and joint non-manipulability**
(Collina, Fullerton, Liu & Weinberg, *Non-manipulability and Approachability Beyond Two-Player
Games*, manuscript (STOC 2027 submission), Lemma 3.1, p.7; proof in A.5, p.26).

Fix a finite game with nonempty action sets and utilities in `[−1, 1]`, and a profile `P` of
learner algorithms whose horizon-`T` menus converge in Hausdorff distance to the (closed)
asymptotic menu `M`. Suppose
1. every `μ ∈ M` has `G_{i,ϕ}(μ) ≤ 0` for every learner `i` and swap `ϕ`;
2. every extreme point `s` of `M` is a product distribution `s = y_s ⊗ q_s` (`y_s ∈ ∆(A₀)`,
   `q_s ∈ ∆(A_L)`) and
   `inf_{y ∈ ∆(A₀)} ‖φ_T(y^{⊗T}, P) − s‖₁ = o(1)`.
Then every learner has no swap regret and the profile is jointly non-manipulable.

**Formalization Note** The asymptotic menu is taken closed: a Hausdorff limit is determined
only up to closure, and the proof uses "the compact convex set M" (p.26). The `o(1)` in
hypothesis 2 is for each extreme point separately. -/
theorem lemma_3_1 [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1)
    (P : Profile A0 Act) (M : Set (A0 × ((i : L) → Act i) → ℝ))
    (hMclosed : IsClosed M) (hM : MenuConvergesTo P M)
    (h1 : ∀ μ ∈ M, ∀ (i : L) (ϕ : Act i → Act i), swapGain u i ϕ μ ≤ 0)
    (h2 : ∀ s ∈ Set.extremePoints ℝ M,
      (∃ (y : A0 → ℝ) (q : ((i : L) → Act i) → ℝ),
        AGT.IsLottery y ∧ AGT.IsLottery q ∧ s = otimes y q) ∧
      ∀ ε > 0, ∃ T0 : ℕ, ∀ T ≥ T0,
        ∃ (y : A0 → ℝ) (hy : AGT.IsLottery y), l1dist (expCSP P (Policy.static y hy T)) s ≤ ε) :
    NoSwapRegret u P ∧ JointlyNonManipulable P := by sorry

end JointNonManip
