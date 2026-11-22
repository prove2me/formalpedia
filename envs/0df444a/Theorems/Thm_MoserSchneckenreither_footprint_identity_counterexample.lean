-- Prove2me | Theorems.Thm_MoserSchneckenreither_footprint_identity_counterexample
-- name    : MoserSchneckenreither.footprint_identity_counterexample
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T08:57:06.617311+00:00
-- url     : https://prove2.me/theorems/bdbbf29a-e612-4478-bd79-83d06042087f
-- title:
--   Lemma 2 — Counterexample with whole-term potential
-- statement:
--   A footprint whose term uses only constructor-like symbols can violate the potential identity of Lemma 2 after a normalised substitution covering its context. The witness instantiates a variable beneath a constructor with a stuck defined normal form.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Counterexample to Lemma 2, pp. 8–9, using the whole-term case distinction of Definition 3, p. 7.

import Definitions.Def_MoserSchneckenreither_Typing

namespace MoserSchneckenreither

theorem footprint_identity_counterexample :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ : Substitution sig) (t : Term sig) (q : Annotation) (k : ℚ≥0),
      σ.Normalised P ∧ (∀ x ∈ Γ.keys, x ∈ σ.domain) ∧
      Typing F .footprint Γ k t q ∧ (∀ f ∈ t.symbols, ConstructorLike P f) ∧
      potential F (t.subst σ.apply) q ≠ contextPotential F σ Γ + k := by sorry

end MoserSchneckenreither
