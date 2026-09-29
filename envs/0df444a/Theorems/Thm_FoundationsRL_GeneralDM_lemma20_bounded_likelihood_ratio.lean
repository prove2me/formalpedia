-- Prove2me | Theorems.Thm_FoundationsRL_GeneralDM_lemma20_bounded_likelihood_ratio
-- name    : FoundationsRL.GeneralDM.lemma20_bounded_likelihood_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T20:24:14.897863+00:00
-- url     : https://prove2.me/theorems/14807859-79bf-43a1-8552-83dc35a167d4
-- title:
--   Lemma 20 — bounded-likelihood-ratio refinement (Eq. 6.7)
-- statement:
--   This theorem formalizes **Lemma 20** (Foster & Rakhlin, *Foundations of Reinforcement
--   Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 96, Eq. (6.7)): let $P, Q$
--   be discrete probability distributions over a finite outcome type $Y$. If
--   $\sup_{F \subseteq Y} P(F)/Q(F) \le V$ for some $V > 0$ (a bounded likelihood ratio), then
--   $$
--   D_{KL}(P \| Q) \le (2 + \log V) \cdot D_H^2(P, Q).
--   $$
--   This refines Lemma 19's $D_H^2 \le D_{KL}$ direction into the opposite direction when the
--   likelihood ratio between $P$ and $Q$ is controlled, and is used in the chain-rule step of
--   Proposition 28's proof.
--
--   **Formalization Note** The book's ratio hypothesis $\sup_F P(F)/Q(F) \le V$ is stated here as
--   $\forall F, P(F) \le V \cdot Q(F)$ (a multiplicative form over $F \in \mathrm{Finset}\,Y$,
--   since $Y$ is finite) rather than a literal division, so that it correctly forces $P(F) = 0$
--   whenever $Q(F) = 0$ — the genuine content of a bounded likelihood ratio. A division-based
--   hypothesis $P(F)/Q(F) \le V$ would instead be vacuously true whenever $Q(F) = 0$ under Lean's
--   $x/0 = 0$ convention, silently permitting an unbounded ratio.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 96, Lemma 20, Eq. (6.7)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace FoundationsRL.GeneralDM

/-- Lemma 20 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision
Making*, arXiv:2312.16730v1, p. 96, Eq. (6.7)): let `P`, `Q` be discrete probability distributions
over a finite outcome type `Y`. If `sup_{F ⊆ Y} P(F)/Q(F) ≤ V` for some `V > 0`, then

`D_KL(P ∥ Q) ≤ (2 + log V) · D²_H(P, Q)`.

**Formalization Note** The book's ratio hypothesis `sup_F P(F)/Q(F) ≤ V` is stated here as
`∀ F, P(F) ≤ V · Q(F)` (multiplicative form) rather than a literal division, so that it correctly
forces `P(F) = 0` whenever `Q(F) = 0` (the genuine content of a bounded likelihood ratio); a
division-based hypothesis `P(F)/Q(F) ≤ V` would instead be vacuously satisfied whenever `Q(F) = 0`
under Lean's `x / 0 = 0` convention, silently permitting an unbounded ratio. `F` ranges over
`Finset Y`, matching "all events" since `Y` is finite (every `Set Y` is a `Finset Y` here). -/
theorem lemma20_bounded_likelihood_ratio {Y : Type*} [Fintype Y] (P Q : Y → ℝ)
    (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1) (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1)
    (V : ℝ) (hV : 0 < V)
    (hratio : ∀ F : Finset Y, (∑ y ∈ F, P y) ≤ V * ∑ y ∈ F, Q y) :
    klDivDiscrete P Q ≤ ENNReal.ofReal ((2 + Real.log V) * hellingerSq P Q) := by sorry

end FoundationsRL.GeneralDM
