-- Prove2me | Theorems.Thm_HamLocality237_Testing_lemma_3_8
-- name    : HamLocality237.Testing.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:30.707445+00:00
-- url     : https://prove2.me/theorems/9d2a1f58-895b-4230-a6ef-76761f954f07
-- title:
--   Lemma 3.8 — the signed commutator inequality
-- statement:
--   For $0<\varepsilon<1/2$ and every $v=q|\perp\rangle+r$, the operator from Equation (18) satisfies
--
--   $$\langle v,i[J_\varepsilon,g]v\rangle\le\eta^2\varepsilon^2|q|^2-|\langle b,r\rangle|^2.$$
--
--   This is the complete inequality $i[J_\varepsilon,g]\preceq\eta^2\varepsilon^2|\perp\rangle\langle\perp|-|b\rangle\langle b|$, including its negative rank-one term.
--
--   Differences from the source:
--   - encoding: a self-adjoint operator inequality on C|⊥⟩ ⊕ L² → the real quadratic-form inequality for every vector of the actual Hilbert direct sum; reason: positivity is equivalent to all quadratic-form inequalities; the scalar and band projections give exactly q and r
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Lemma 3.8, Eq. (24), p.20. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory
open scoped BigOperators

namespace HamLocality237.Testing

theorem lemma_3_8 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (v : SingleRegister) :
    (inner ℂ v ((Complex.I • (hardOperator ε * singleCorrection -
      singleCorrection * hardOperator ε)) v)).re ≤
      etaSquared * ε ^ 2 * ‖scalarPart v‖ ^ 2 - ‖inner ℂ bumpVector (bandPart v)‖ ^ 2 := by sorry

end HamLocality237.Testing
