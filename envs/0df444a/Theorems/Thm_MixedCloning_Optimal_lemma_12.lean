-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_12
-- name    : MixedCloning.Optimal.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:04:40.264893+00:00
-- url     : https://prove2.me/theorems/4d6d0ae7-8e10-4c87-8b3f-eaa2f74c4d54
-- title:
--   Lemma 12 — fidelity is bounded by projector overlap
-- statement:
--   Let $\Pi$ be an orthogonal projector of rank $R$ on $\mathbb C^d$, and let $\sigma$ be a quantum state. With the squared-fidelity convention,
--
--   $$F(\sigma,\Pi/R)\le\operatorname{tr}(\sigma\Pi).$$
--
--   This replaces a nonlinear fidelity objective by the linear overlap with the target support. The formula also holds for the zero projector, where scalar division and fidelity both evaluate to zero.
--
--   Differences from the source:
--   - generalization: projector-state fidelity for Π/R → the squared-fidelity matrix formula, also at R=0; reason: the positive-rank cases are unchanged and the zero-projector inequality is 0 ≤ 0
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 17, Lemma 12

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_12 (d R : ℕ) (P sigma : Op (Fin d))
    (hP : IsProjector R P) (hsigma : IsState sigma) :
    fidelity sigma (projectorState R P) ≤ (sigma * P).trace.re := by sorry

end MixedCloning.Optimal
