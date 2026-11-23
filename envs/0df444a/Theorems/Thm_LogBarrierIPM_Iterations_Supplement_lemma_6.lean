-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_lemma_6
-- name    : LogBarrierIPM.Iterations.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:13:06.432951+00:00
-- url     : https://prove2.me/theorems/bbc88238-41ee-471c-ae04-f01571d0748e
-- title:
--   Lemma 6 — valuation on the nonnegative Puiseux semifield
-- statement:
--   On $K_+$, the valuation is monotone, onto $\mathbb T$, and preserves the semifield operations:
--   $$\operatorname{val}(f+g)=\max(\operatorname{val}f,\operatorname{val}g),\qquad \operatorname{val}(fg)=\operatorname{val}f+\operatorname{val}g.$$
--   It sends zero to $-\infty$ and one to $0$, and for $f>0$ it sends inversion to tropical inversion. The statement supplies sum, product and inverse series and asserts the identities for every series with the requisite eventual evaluations. The homomorphism transfers nonnegative polyhedral generation to tropical generation.
--
--   Differences from the source:
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
--   - encoding: a semifield homomorphism defined on K_+ → seven explicit clauses, including existence of sum, product and positive inverse series; reason: K is a structure of coefficient functions without field operations, so closure is asserted rather than assumed
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 10, Lemma 6

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_PuiseuxGeometry

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem lemma_6 :
    (∀ f g : Puiseux, KNonneg f → KNonneg g → KLe f g → f.val ≤ g.val) ∧
    (∀ a : WithBot ℝ, ∃ f : Puiseux, KNonneg f ∧ f.val = a) ∧
    (∃ z : Puiseux, (∀ a, z.coeff a = 0) ∧ z.val = ⊥) ∧
    (∃ o : Puiseux, (∀ᶠ t in atTop, o.eval t = 1) ∧ o.val = 0) ∧
    (∀ f g : Puiseux, KNonneg f → KNonneg g →
      (∃ h : Puiseux, ∀ᶠ t in atTop, h.eval t = f.eval t + g.eval t) ∧
      ∀ h : Puiseux, (∀ᶠ t in atTop, h.eval t = f.eval t + g.eval t) →
        KNonneg h ∧ h.val = max f.val g.val) ∧
    (∀ f g : Puiseux, KNonneg f → KNonneg g →
      (∃ h : Puiseux, ∀ᶠ t in atTop, h.eval t = f.eval t * g.eval t) ∧
      ∀ h : Puiseux, (∀ᶠ t in atTop, h.eval t = f.eval t * g.eval t) →
        KNonneg h ∧ h.val = f.val + g.val) ∧
    (∀ f : Puiseux, KPositive f →
      (∃ h : Puiseux, ∀ᶠ t in atTop, f.eval t * h.eval t = 1) ∧
      ∀ h : Puiseux, (∀ᶠ t in atTop, f.eval t * h.eval t = 1) →
        KPositive h ∧ f.val + h.val = 0) := by sorry

end LogBarrierIPM.Iterations.Supplement
