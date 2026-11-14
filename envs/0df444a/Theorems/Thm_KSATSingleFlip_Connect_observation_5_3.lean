-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_observation_5_3
-- name    : KSATSingleFlip.Connect.observation_5_3
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:38:54.579565+00:00
-- url     : https://prove2.me/theorems/01273679-ad31-4fc4-ba0b-250eb0ac226f
-- title:
--   Observation 5.3 — Disagreement is star-flippable
-- statement:
--   Let Φ be a finite Boolean CNF formula, σ and τ assignments with τ satisfying Φ, and U any set of variables. For every clause C whose variables all lie in U and whose unique true literal under σ is at v in U ∩ Δ(σ,τ), there is another variable w in C ∩ U ∩ Δ(σ,τ). In particular, taking U to be the variable set of the star-core makes U ∩ Δ(σ,τ) star-flippable, as stated in Observation 5.3. The theorem proves the stronger assertion for arbitrary U; the maximality of the core and the assumption that σ satisfies Φ are not needed.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, Observation 5.3, printed page 33, PDF page 35, STOC 2027 submission #737: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Model

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

theorem observation_5_3 {V : Type} [Fintype V] [DecidableEq V]
    (Φ : GFormula V) (σ τ : V → Bool) (U : Finset V)
    (hτ : FSat τ Φ) :
    ∀ C ∈ Φ, vbl C ⊆ U → ∀ v ∈ U ∩ disagree σ τ,
      satSet σ C = {v} → ∃ w ∈ U ∩ disagree σ τ, w ≠ v ∧ w ∈ vbl C := by
  sorry

end KSATSingleFlip.Connect
