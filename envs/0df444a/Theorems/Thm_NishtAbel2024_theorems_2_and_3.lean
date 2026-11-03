-- Prove2me | Theorems.Thm_NishtAbel2024_theorems_2_and_3
-- name    : NishtAbel2024.theorems_2_and_3
-- status  : Disproved
-- author  : @kmehltretter82
-- created : 2026-10-31T19:04:20.923012+00:00
-- url     : https://prove2.me/theorems/c44793d0-3bc7-4d70-a7a8-16d57600fda2
-- title:
--   Semantic Soundness of Size Judgments (Theorem 2) and Expression/Clause Typing (Theorem 3)
-- statement:
--   Theorems 2 and 3 (Sections 5.4.1 & 5.4.3, pp. 35–37): (1) semantic monotonicity and soundness of syntactic size well-formedness (`SizeWf`), weak inequality (`SizeLe`), and strict inequality (`SizeLt`) under ordered size valuations `SizeValLe Ψ ρ ρ'`; and (2) the Fundamental Theorem of Reducibility (`SemExprTyping` and `SemClausesTyping`) for well-typed expressions and copattern clauses under guarded recursive block validity.
--
--   **Superseded.** This is the first formalization of Theorems 2–3 (pp. 36–37) of
--   the thesis. It is refuted through its Theorem 3 conjunct by the disproof
--   `33af96b2-4760-46a4-b568-514c51eb7ee9`: the existing signature declares a function of unit type
--   with no clauses, and the new block declares a function with the same name whose
--   clause calls it. The signature alone is valid and the reference is typable, but
--   with the block present the reference reduces to itself forever, so it is not in
--   the interpretation of the unit type. The thesis assumes that existing functions
--   were checked earlier and cannot refer to the current block (§5.4.2); the formal
--   statement does not. Corrected statement: `NishtAbel2024V2.theorems_2_and_3`. It
--   assumes a well-scoped block extension (`scopeBlockExtension`) and uses revised
--   semantics for quantifiers and inductive types, which also resolve two further
--   checked counterexamples to the original Theorem 3.
-- source:
--   Kanstantsin Nisht, 'Type-Based Termination Checking in Agda', Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, 30th International Conference on Types for Proofs and Programs (TYPES 2024). Section 5.4, Theorem 2 (p. 35) and Theorem 3 (pp. 36–37).

import Definitions.Def_NishtAbel2024_Syntax
import Definitions.Def_NishtAbel2024_Semantics

namespace NishtAbel2024

/-- Theorem 2 (Soundness of kind-level judgments, p. 36) and
Theorem 3 (Soundness of expression typing in System `F_ω^{cop, SCT}`, pp. 36–37):
1. (**Theorem 2**) For any well-formed size context `⊢ Ψ` and ordered valuations
   `ρ ≤ ρ' ∈ ⟦Ψ⟧`:
   - `Ψ ⊢ a ⟹ ⟦a⟧_ρ ≤ ⟦a⟧_{ρ'}`
   - `Ψ ⊢ a ≤ b ⟹ ⟦a⟧_ρ ≤ ⟦b⟧_{ρ'}`
   - `Ψ ⊢ a < b ⟹ ⟦a⟧_ρ < ⟦b⟧_{ρ'}`.
2. (**Theorem 3**) Under semantic validity `⊨ Σ`, well-formed contexts `⊢ Δ`, `Δ ⊢ Γ`,
   `Δ ⊢ C ⇐ *`, `⊢ G`, and guarded block validity `G, ⟦Ψ_f⟧ ⊨ Ξ`, bidirectional expression
   inference, expression checking, and clause checking imply semantic membership in the
   reducibility candidate `⟦C⟧`. -/
theorem theorems_2_and_3 :
    (∀ (Ψ : SizeCtx) (ρ ρ' : SizeVal),
      SizeCtxWf Ψ →
      SizeValLe Ψ ρ ρ' →
      (∀ a : SizeExp, SizeWf Ψ a → SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' a)) ∧
      (∀ a b : SizeExp, SizeLe Ψ a b → SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' b)) ∧
      (∀ a b : SizeExp, SizeLt Ψ a b → SizeOrd.lt (evalSizeExp ρ a) (evalSizeExp ρ' b))) ∧
    (∀ (Ω : TypingEnv) (Δ : KindingCtx) (Γ : TermCtx) (C : TypeExpr),
      SemSigValid Ω.sig →
      SizeCtxWf Δ.sizes →
      TermCtxWf Δ Γ →
      KindCheck Δ C .star →
      SCTValid Ω.graphs →
      (∀ ρ ∈ evalKindingCtx Δ,
        SemBlockGuardedValid Ω.sig Ω.block Ω.graphs Ω.caller Ω.callerSizes ρ) →
      (∀ r : Term, ExprInfer Ω Δ Γ r C → SemExprTyping Ω.sig Ω.block Δ Γ r C) ∧
      (∀ r : Term, ExprCheck Ω Δ Γ r C → SemExprTyping Ω.sig Ω.block Δ Γ r C) ∧
      (∀ Ds : List Clause,
        (∀ D ∈ Ds, ClauseCheck Ω Δ Γ D C) →
        SemClausesTyping Ω.sig Ω.block Δ Γ Ds C)) := by
  sorry

end NishtAbel2024
