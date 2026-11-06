-- Prove2me | Theorems.Thm_JointNonManip_display_6
-- name    : JointNonManip.display_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:14.985281+00:00
-- url     : https://prove2.me/theorems/d67f8348-a578-438a-9622-8743c0d9aba2
-- title:
--   Display (6), p.27 — the commitment-phase bound $\|\sum_{t\in I}k^{(t)}-\ell(y_j\otimes q_j)\|_1\le\|\sum_{t\in I}(e_{c^{(t)}}-z_j)\|_1+\ell\|z_j-y_j\|_1\le m+\ell\varepsilon$
-- statement:
--   Let $q=\bigotimes_i x_i$ be a product of lotteries on the learners' action sets, $y_j,z_j\in\Delta(A_0)$, $I$ a finite set of $\ell=|I|$ rounds and $c^{(t)}\in A_0$ the optimizer's actions in them. Then, with $k^{(t)}=e_{c^{(t)}}\otimes q$,
--   $$
--   \Big\|\sum_{t\in I}k^{(t)}-\ell\,(y_j\otimes q)\Big\|_1\le\Big\|\sum_{t\in I}\big(e_{c^{(t)}}-z_j\big)\Big\|_1+\ell\,\|z_j-y_j\|_1 ,
--   $$
--   and if the test $\|\sum_{t\in I}(e_{c^{(t)}}-z_j)\|_1\le m$ passed and the codebook has $\|z_j-y_j\|_1\le\varepsilon$, the left side is at most $m+\ell\varepsilon$.
--
--   This bounds the distance of the committed phase from the listed Nash-response outcome in the proof of Lemma A.4.
--
--   Differences from the source:
--   - generalization: the ℓ committed rounds I through the last passed test, on which the learners play q_j → any finite set I of rounds, any actions c(t), any product q of lotteries and any lotteries y, z; reason: the inequality uses only that q is a probability vector; it specializes to the committed rounds
--   - encoding: ≤ m + ℓε, by the passed test and ‖z_j − y_j‖₁ ≤ ε → for all m, ε: ‖∑_{t∈I}(e_{c(t)} − z)‖₁ ≤ m → ‖z − y‖₁ ≤ ε → left side ≤ m + ℓε; reason: the test condition and the codebook bound, in force in the source, as hypotheses
--   - encoding: learners L = {1, …, n − 1}, finite action sets A₀, Aᵢ (a finite normal-form game, p.4) → a finite type L of learners (empty when n = 1) and finite nonempty types A0, Act i; reason: relabeling; ∆(Aᵢ) is empty unless Aᵢ is nonempty, so nonemptiness is part of the source's model
--   - encoding: CSPs µ ∈ ∆(A) ⊂ ℝ^A, y ⊗ q, ⟨·,·⟩, q = ⊗ᵢ xᵢ ∈ ∆(A_L), ℓ₁ and ℓ₂ norms → real functions on A0 × ((i : L) → Act i); otimes, pairing; AGT.profileProb x of a profile of lotteries AGT.IsLottery; explicit sums l1dist, l2dist; reason: Lean representation of the same objects
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), proof of Lemma A.4, display (6), p.27

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

namespace JointNonManip

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Display (6): the commitment-phase bound** (Collina, Fullerton, Liu & Weinberg,
*Non-manipulability and Approachability Beyond Two-Player Games*, manuscript (STOC 2027
submission), proof of Lemma A.4, display (6), p.27).

Let `q = ⊗ᵢ xᵢ` be a product of lotteries, `y, z ∈ ∆(A₀)`, `I` a finite set of `ℓ = |I|` rounds
and `c(t) ∈ A₀` the optimizer's actions. Then
`‖∑_{t∈I} e_{c(t)} ⊗ q − ℓ (y ⊗ q)‖₁ ≤ ‖∑_{t∈I} (e_{c(t)} − z)‖₁ + ℓ ‖z − y‖₁`,
and hence, if `‖∑_{t∈I} (e_{c(t)} − z)‖₁ ≤ m` (the passed test) and `‖z − y‖₁ ≤ ε` (the
codebook), the left side is at most `m + ℓε`. -/
theorem display_6 (x : (i : L) → Act i → ℝ) (hx : AGT.IsMixedProfile x)
    (y z : A0 → ℝ) (hy : AGT.IsLottery y) (hz : AGT.IsLottery z)
    (I : Finset ℕ) (c : ℕ → A0) :
    l1dist (∑ t ∈ I, otimes (pointMass (c t)) (AGT.profileProb x))
        ((I.card : ℝ) • otimes y (AGT.profileProb x)) ≤
      l1dist (∑ t ∈ I, (pointMass (c t) - z)) 0 + (I.card : ℝ) * l1dist z y ∧
    ∀ m ε : ℝ, l1dist (∑ t ∈ I, (pointMass (c t) - z)) 0 ≤ m → l1dist z y ≤ ε →
      l1dist (∑ t ∈ I, otimes (pointMass (c t)) (AGT.profileProb x))
        ((I.card : ℝ) • otimes y (AGT.profileProb x)) ≤ m + (I.card : ℝ) * ε := by sorry

end JointNonManip
