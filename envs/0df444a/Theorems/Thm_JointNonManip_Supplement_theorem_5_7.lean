-- Prove2me | Theorems.Thm_JointNonManip_Supplement_theorem_5_7
-- name    : JointNonManip.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:30:09.820172+00:00
-- url     : https://prove2.me/theorems/a14916f4-bd7d-4e2a-912a-a83afdbdda94
-- title:
--   Theorem 5.7 — a convex compact set is jointly approachable by independent learners iff it is jointly halfspace satisfiable
-- statement:
--   Let $G$ be a finite game with optimizer action set $A_0$ and independent learners $i\in L$ with action sets $A_i$, all nonempty, and let $g:A_0\times A_L\to\mathbb R^d$ be a vector statistic. Let $S\subseteq\mathbb R^d$ be nonempty, convex and compact. Then
--
--   $$S\ \text{is jointly approachable by the learners}\iff S\ \text{is jointly halfspace satisfiable},$$
--
--   that is, some profile of independent learning algorithms drives $\mathbb E[\operatorname{dist}(\bar g_T,S)]\to0$ against every optimizer policy if and only if for every $U\in\mathbb R^d$ some product distribution $q=\bigotimes_i x_i$ satisfies $\langle U,g(y,q)\rangle\le\max_{s\in S}\langle U,s\rangle$ for all $y\in\Delta(A_0)$. Moreover, when $S$ is jointly halfspace satisfiable, it is approached by a profile whose mixed strategies depend only on the optimizer's past actions.
--
--   The theorem extends Blackwell's characterization to several learners without shared randomness: the feasible joint strategies form the nonconvex set of product distributions, the halfspace condition still characterizes approachability, while the response condition does not (Lemma 5.8).
--
--   **Formalization Note** Necessity is stated for profiles whose lotteries may depend on the whole realized past (the largest class of independent learners); sufficiency is also given by a public-history profile, the class of Algorithm 2.
--
--   Differences from the source:
--   - reading: a convex and compact set S, with max over S and dist(·, S) → S.Nonempty as a hypothesis; reason: both Definition 5.5 (max over S) and Definition 5.2 (dist to S) presuppose S ≠ ∅, and in Lean the distance to ∅ is 0, which would make ∅ trivially approachable
--   - generalization: "a profile of independent learning algorithms", class of learner algorithms not pinned down → necessity for every profile whose lotteries are functions of the whole realized past; sufficiency additionally by a profile depending only on the optimizer's past actions; reason: this covers every reading between the public-history class of Algorithm 2 and the full-history class, so it specializes to the source's theorem for each of them
--   - encoding: ℝ^d, Euclidean dist, max_{s∈S}⟨U, s⟩, E[·] → EuclideanSpace ℝ (Fin d), Metric.infDist, real sSup of the image (the maximum for nonempty compact S), finite sums over length-T trajectories; reason: Lean conventions; same instances
--   - encoding: optimizer policy π that observes the learners' current product distribution → an anytime policy choosing a lottery on A₀ from the whole realized past; reason: the current product distribution is a function of that past and the fixed profile
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), Theorem 5.7, p.13; Definitions 5.2 and 5.5, pp.12–13; proof and Algorithm 2, Appendix A.9, pp.30–32

import Mathlib
import Definitions.Def_JointNonManip_Supplement_JointApproach

namespace JointNonManip.Supplement

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Theorem 5.7: joint approachability of convex sets** (Collina, Fullerton, Liu & Weinberg,
*Non-manipulability and Approachability Beyond Two-Player Games*, manuscript (STOC 2027
submission), Theorem 5.7, p.13; Definitions 5.2 and 5.5, pp.12–13; proof in Appendix A.9,
pp.30–31).

Let `g : A₀ × A_L → ℝ^d` be a vector statistic of a finite game with nonempty action sets. A
nonempty convex compact set `S ⊆ ℝ^d` is jointly approachable by a profile of independent
learners if and only if it is jointly halfspace satisfiable; when it is, a profile whose
lotteries depend only on the optimizer's past actions approaches it.

**Formalization Note** `S` is assumed nonempty: Definition 5.5 writes `max_{s ∈ S}` and
Definition 5.2 writes `dist(·, S)`, both of which presuppose `S ≠ ∅` (in Lean the distance to `∅`
is `0`, which would make `∅` trivially approachable). Learner profiles may depend on the whole
realized past (the largest class of independent learners), and the second conjunct gives the
sufficiency direction already in the public-history class of Algorithm 2; optimizer policies are
anytime and adaptive (see `IndepProfile`, `AnytimePolicy`). -/
theorem theorem_5_7 [Nonempty A0] [∀ i, Nonempty (Act i)] {d : ℕ}
    (g : A0 × ((i : L) → Act i) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d))) (hconv : Convex ℝ S) (hcpt : IsCompact S)
    (hne : S.Nonempty) :
    (IsJointlyApproachable g S ↔ IsJointlyHalfspaceSatisfiable g S) ∧
      (IsJointlyHalfspaceSatisfiable g S →
        ∃ P : IndepProfile A0 Act, IsPublicHistory P ∧ Approaches g S P) := by sorry

end JointNonManip.Supplement
