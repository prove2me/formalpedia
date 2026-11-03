-- Prove2me | Theorems.Thm_NishtAbel2024V2_theorems_2_and_3
-- name    : NishtAbel2024V2.theorems_2_and_3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-02T21:45:45.278197+00:00
-- url     : https://prove2.me/theorems/158c09ed-dfc9-4db1-b33d-0cbbd6ed7779
-- title:
--   Repaired V2 Semantic Soundness of Size Judgments (Theorem 2) and Expression/Clause Typing (Theorem 3)
-- statement:
--   Repaired V2 formulation of Theorem 2 (p. 36) and Theorem 3 (pp. 36–37) of Nisht & Abel (2024): (1) well-formed size expressions and size inequalities are monotonic and sound in `SizeOrd`; (2) under a well-scoped block extension `scopeBlockExtension Ω.sig Ω.block` and ambient signature validity `SemSigValidIn Ω.sig Ω.block` over the repaired V2 arbitrary-type-tag quantifier and global-closure `μ` semantics, bidirectional expression and clause typing imply parametric semantic membership `SemExprTypingWith`.
--
--   **Differences from the thesis.** Theorem 3 assumes a well-scoped block extension (`scopeBlockExtension`) and validity of the existing signature in the world that includes the block (`SemSigValidIn`), and it uses revised semantics for quantifiers (arbitrary type tags) and for inductive types (global-closure $\mu$). This statement replaces the refuted `NishtAbel2024.theorems_2_and_3`.
-- source:
--   Kanstantsin Nisht, "Type-Based Termination Checking in Agda", Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, TYPES 2024. Repaired V2 formalization.

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Semantics

namespace NishtAbel2024V2

/-- Repaired Theorem2 (Soundness of kind-level judgments, p. 36) and
Theorem 3 (Soundness of expression typing in System `F_ω^{cop, SCT}`, pp. 36–37) in `NishtAbel2024V2`:
1. (**Theorem 2**) For any well-formed size context `⊢ Ψ` and ordered valuations
   `ρ ≤ ρ' ∈ ⟦Ψ⟧`:
   - `Ψ ⊢ a ⟹ ⟦a⟧_ρ ≤ ⟦a⟧_{ρ'}`
   - `Ψ ⊢ a ≤ b ⟹ ⟦a⟧_ρ ≤ ⟦b⟧_{ρ'}`
   - `Ψ ⊢ a < b ⟹ ⟦a⟧_ρ < ⟦b⟧_{ρ'}`.
2. (**Theorem 3**) Under well-scoped block extension `scopeBlockExtension Ω.sig Ω.block`,
   ambient semantic validity `SemSigValidIn Ω.sig Ω.block`, well-formed contexts `⊢ Δ`, `Δ ⊢ Γ`,
   `Δ ⊢ C ⇐ *`, `⊢ G`, and guarded block validity `G, ⟦Ψ_f⟧ ⊨ Ξ` over the repaired V2
   arbitrary-type-tag quantifier and global-closure `μ` semantics, bidirectional expression
   inference, expression checking, and clause checking imply semantic membership in `⟦C⟧`. -/
theorem theorems_2_and_3 :
    (∀ (Ψ : SizeCtx) (ρ ρ' : SizeVal),
      SizeCtxWf Ψ →
      SizeValLe Ψ ρ ρ' →
      (∀ a : SizeExp, SizeWf Ψ a → SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' a)) ∧
      (∀ a b : SizeExp, SizeLe Ψ a b → SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' b)) ∧
      (∀ a b : SizeExp, SizeLt Ψ a b → SizeOrd.lt (evalSizeExp ρ a) (evalSizeExp ρ' b))) ∧
    (∀ (Ω : TypingEnv) (Δ : KindingCtx) (Γ : TermCtx) (C : TypeExpr),
      scopeBlockExtension Ω.sig Ω.block →
      SemSigValidIn Ω.sig Ω.block →
      SizeCtxWf Δ.sizes →
      TermCtxWf Δ Γ →
      KindCheck Δ C .star →
      SCTValid Ω.graphs →
      (∀ ρ ∈ evalKindingCtx Δ,
        SemBlockGuardedValid Ω.sig Ω.block Ω.graphs Ω.caller Ω.callerSizes ρ) →
      (∀ r : Term, ExprInfer Ω Δ Γ r C → SemExprTypingWith Ω.sig Ω.block Δ Γ r C) ∧
      (∀ r : Term, ExprCheck Ω Δ Γ r C → SemExprTypingWith Ω.sig Ω.block Δ Γ r C) ∧
      (∀ Ds : List Clause,
        (∀ D ∈ Ds, ClauseCheck Ω Δ Γ D C) →
        SemClausesTyping Ω.sig Ω.block Δ Γ Ds C)) := by
  sorry

end NishtAbel2024V2
