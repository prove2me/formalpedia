-- Prove2me | Theorems.Thm_JointNonManip_sne_extreme_points
-- name    : JointNonManip.sne_extreme_points
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:08.429627+00:00
-- url     : https://prove2.me/theorems/713a57c5-f613-451b-93b3-a953e1b152d8
-- title:
--   §3, p.8 — every extreme point of $S_{\mathrm{NE}}(G_{\mathcal L})$ is a product $y\otimes q$ with $q\in\mathrm{NE}(G_{\mathcal L}(y))$
-- statement:
--   Let $G$ be a finite game with nonempty action sets and learner utilities in $[-1,1]$. Every extreme point $s$ of $S_{\mathrm{NE}}(G_{\mathcal L})$ is a product distribution
--   $$
--   s=y\otimes q,\qquad y\in\Delta(A_0),\quad q=\textstyle\bigotimes_{i\in\mathcal L}x_i\in\mathrm{NE}(G_{\mathcal L}(y)).
--   $$
--
--   Together with the static attainability of Lemma A.4, this is the second menu property of Lemma 3.1.
--
--   Differences from the source:
--   - generalization: every extreme point of S_NE(G_L) is a product distribution → every extreme point is y ⊗ (⊗ᵢ xᵢ) with y a lottery and x a mixed Nash equilibrium of G_L(y); reason: a stronger conclusion that implies the product form; it is what 'by definition' refers to
--   - encoding: learners L = {1, …, n − 1}, finite action sets A₀, Aᵢ (a finite normal-form game, p.4) → a finite type L of learners (empty when n = 1) and finite nonempty types A0, Act i; reason: relabeling; ∆(Aᵢ) is empty unless Aᵢ is nonempty, so nonemptiness is part of the source's model
--   - encoding: CSPs µ ∈ ∆(A) ⊂ ℝ^A, y ⊗ q, ⟨·,·⟩, q = ⊗ᵢ xᵢ ∈ ∆(A_L), ℓ₁ and ℓ₂ norms → real functions on A0 × ((i : L) → Act i); otimes, pairing; AGT.profileProb x of a profile of lotteries AGT.IsLottery; explicit sums l1dist, l2dist; reason: Lean representation of the same objects
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), §3, p.8 ('Every extreme point of SNE(GL) is a product distribution by definition')

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

namespace JointNonManip

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Every extreme point of `S_NE(G_L)` is a product distribution** `y ⊗ q` with
`y ∈ ∆(A₀)` and `q ∈ NE(G_L(y))` (Collina, Fullerton, Liu & Weinberg, *Non-manipulability and
Approachability Beyond Two-Player Games*, manuscript (STOC 2027 submission), §3, p.8: "Every
extreme point of SNE(GL) is a product distribution by definition").

**Formalization Note** The conclusion also records that the product's learner factor is a Nash
equilibrium of the induced game `G_L(y)`, which is what "by definition" refers to. -/
theorem sne_extreme_points [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1) :
    ∀ s ∈ Set.extremePoints ℝ (SNE u), ∃ (y : A0 → ℝ) (x : (i : L) → Act i → ℝ),
      AGT.IsLottery y ∧ AGT.IsMixedNash (inducedUtility u y) x ∧
        s = otimes y (AGT.profileProb x) := by sorry

end JointNonManip
