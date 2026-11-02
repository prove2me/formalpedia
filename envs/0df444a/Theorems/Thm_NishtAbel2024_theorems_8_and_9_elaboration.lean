-- Prove2me | Theorems.Thm_NishtAbel2024_theorems_8_and_9_elaboration
-- name    : NishtAbel2024.theorems_8_and_9_elaboration
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T23:17:09.312055+00:00
-- url     : https://prove2.me/theorems/39f8b202-360d-4367-9d34-d457841d2a8f
-- title:
--   Pattern and copattern spine elaboration (Theorems 8–9, existing model)
-- statement:
--   Every derivation of pattern inference produces an annotated pattern with the corresponding pattern-typing derivation, preserving the generated type and term contexts. Every derivation of copattern-spine inference likewise produces a well-typed annotated spine with the same input type, residual type, and generated contexts. These are exactly the third and fourth conjuncts of the existing bundled mission theorem. No extra hypotheses or restricted syntax are added. This result concerns the published inference and typing definitions, including their existing bound normalization; it does not establish signature encoding, the polarity-classification lemmas, general capture-avoiding substitution, or semantic soundness.
-- source:
--   Kanstantsin Nisht, Type-Based Termination Checking in Agda, 2024, Section 6.2, Theorems 8 and 9, printed p.45, https://knisht.github.io/agda/msc.pdf; exact third/fourth formal conjuncts of Prove2Me theorem 60c982ad-4712-4445-8689-70bbff93fcd9.

import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024

theorem theorems_8_and_9_elaboration :
(∀ (Δ₀ : KindingCtx) (p p' : Pat) (A : TypeExpr)
      (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferPat Δ₀ p A Γ Δ Ψ p' → PatTyping Δ₀ Δ Γ p' A) ∧
    (∀ (Δ₀ : KindingCtx) (qs qs' : PatSpine) (A C : TypeExpr)
      (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferSpine Δ₀ qs A C Γ Δ Ψ qs' → SpineTyping Δ₀ Δ Γ A qs' C) := by sorry

end NishtAbel2024
