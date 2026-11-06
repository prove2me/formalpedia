-- Prove2me | Theorems.Thm_JointNonManip_approx_nash_near_ENE
-- name    : JointNonManip.approx_nash_near_ENE
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:14.292197+00:00
-- url     : https://prove2.me/theorems/b53dacda-d77d-47fd-9181-afb3efedd9f1
-- title:
--   Proof of Lemma A.4, p.27 — $d_T=o(1)$: approximate Nash responses are uniformly close to $E_{\mathrm{NE}}$
-- statement:
--   Let $G$ be a finite game with nonempty action sets and learner utilities in $[-1,1]$. For every $\varepsilon>0$ there is $\delta>0$ such that for every $y\in\Delta(A_0)$ and every profile of lotteries $x=(x_i)_{i\in\mathcal L}$ whose pure deviation gains in the induced game are all at most $\delta$,
--   $$
--   u_i^{y}(b_i,x_{-i})-u_i^{y}(x)\le\delta\qquad\text{for every } i\in\mathcal L,\ b_i\in A_i,
--   $$
--   the product $y\otimes q$, $q=\bigotimes_i x_i$, is within $\ell_1$ distance $\varepsilon$ of $E_{\mathrm{NE}}$: $\operatorname{dist}_1(y\otimes q,E_{\mathrm{NE}})\le\varepsilon$.
--
--   In the proof of Lemma A.4 the codebook retains the grid profiles $(y_j,x_j)$ whose deviation gains are at most $2\varepsilon_T\to0$; the statement gives $d_T=\max_j\operatorname{dist}_1(y_j\otimes q_j,E_{\mathrm{NE}})=o(1)$. The modulus $\delta$ depends on the game.
--
--   Differences from the source:
--   - generalization: d_T = max_j dist₁(y_j ⊗ q_j, E_NE) = o(1) for the grid profiles retained with threshold 2ε, ε = 1/⌈log(T + 2)⌉ → ∀ ε > 0, ∃ δ > 0: every (y, x) of lotteries with all pure deviation gains ≤ δ has y ⊗ q within ℓ₁ distance ε of E_NE; reason: the compactness argument on p.27 is uniform over approximate Nash responses; the retained entries have deviation gains ≤ 2ε_T → 0, so d_T ≤ ε for large T
--   - encoding: dist₁(µ, E_NE) ≤ ε → ∃ s ∈ E_NE with l1dist µ s ≤ ε; reason: E_NE is compact, so the infimum is attained
--   - encoding: learners L = {1, …, n − 1}, finite action sets A₀, Aᵢ (a finite normal-form game, p.4) → a finite type L of learners (empty when n = 1) and finite nonempty types A0, Act i; reason: relabeling; ∆(Aᵢ) is empty unless Aᵢ is nonempty, so nonemptiness is part of the source's model
--   - encoding: CSPs µ ∈ ∆(A) ⊂ ℝ^A, y ⊗ q, ⟨·,·⟩, q = ⊗ᵢ xᵢ ∈ ∆(A_L), ℓ₁ and ℓ₂ norms → real functions on A0 × ((i : L) → Act i); otimes, pairing; AGT.profileProb x of a profile of lotteries AGT.IsLottery; explicit sums l1dist, l2dist; reason: Lean representation of the same objects
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), proof of Lemma A.4, p.27, "Moreover, dT := maxj dist1(yj ⊗ qj, ENE) = o(1)"

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

namespace JointNonManip

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Approximate Nash responses are close to `E_NE`** (Collina, Fullerton, Liu & Weinberg,
*Non-manipulability and Approachability Beyond Two-Player Games*, manuscript (STOC 2027
submission), proof of Lemma A.4, p.27: "dT := maxj dist1(yj ⊗ qj, ENE) = o(1). Indeed, any
contrary sequence has a convergent subsequence of strategy profiles. The limit satisfies all
Nash inequalities, so its joint outcome belongs to ENE").

For the fixed game (nonempty finite action sets, learner utilities in `[−1, 1]`): for every
`ε > 0` there is `δ > 0` such that for every `y ∈ ∆(A₀)` and every profile of lotteries `x`
whose pure deviation gains in the induced game `G_L(y)` are all at most `δ`,
`u_i^y(bᵢ, x_{−i}) − u_i^y(x) ≤ δ` for all `i ∈ L`, `bᵢ ∈ Aᵢ`, the product `y ⊗ (⊗ᵢ xᵢ)` is within
ℓ₁ distance `ε` of `E_NE`.

**Formalization Note** This is the uniform form of `d_T = o(1)`: the grid entries retained with
threshold `2ε_T → 0` satisfy the hypothesis for large `T`, so `d_T ≤ ε`. `δ` depends on the game
(p.38: "the compactness argument gives no game-uniform modulus"). -/
theorem approx_nash_near_ENE [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1) :
    ∀ ε > 0, ∃ δ > 0, ∀ (y : A0 → ℝ) (x : (i : L) → Act i → ℝ),
      AGT.IsLottery y → AGT.IsMixedProfile x →
      (∀ (i : L) (b : Act i),
        AGT.expectedPayoff (inducedUtility u y) (Function.update x i (pointMass b)) i -
          AGT.expectedPayoff (inducedUtility u y) x i ≤ δ) →
      ∃ s ∈ ENE u, l1dist (otimes y (AGT.profileProb x)) s ≤ ε := by sorry

end JointNonManip
