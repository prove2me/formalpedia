-- Prove2me | Theorems.Thm_HamLocality237_Testing_lemma_3_7
-- name    : HamLocality237.Testing.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:15.566399+00:00
-- url     : https://prove2.me/theorems/47d50731-d997-41f7-a139-1729da27ab55
-- title:
--   Lemma 3.7 — full L² variational maximum with attainment
-- statement:
--   For every $r\in L^2([-1/2,1/2])$, the correction operator has
--
--   $$\langle r,gr\rangle=\max_{u\in L^2(\mathbb R_+)}\{\|Or+Ru\|^2-\eta^2\|u\|^2\}.$$
--
--   The entire L² space is used, and some $u$ attains the value. The quadratic form uses the L² summand of $g$; no finite or discrete class of controls replaces the supremum.
--
--   Differences from the source:
--   - encoding: a supremum together with an attaining vector → IsGreatest of the real range of the variational expression; reason: IsGreatest asserts both the upper bound and membership in the range; the real part is the real quadratic form of the self-adjoint correction
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Lemma 3.7, Eq. (23), p.19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory
open scoped BigOperators

namespace HamLocality237.Testing

theorem lemma_3_7 (r : BandSpace) :
    IsGreatest (Set.range (fun u : HalfLineSpace =>
      ‖observationOperator r + responseOperator u‖ ^ 2 - etaSquared * ‖u‖ ^ 2))
      (inner ℂ r (bandCorrection r)).re := by sorry

end HamLocality237.Testing
