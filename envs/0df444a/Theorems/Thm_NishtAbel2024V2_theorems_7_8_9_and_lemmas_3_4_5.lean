-- Prove2me | Theorems.Thm_NishtAbel2024V2_theorems_7_8_9_and_lemmas_3_4_5
-- name    : NishtAbel2024V2.theorems_7_8_9_and_lemmas_3_4_5
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T21:46:01.492832+00:00
-- url     : https://prove2.me/theorems/44a1497d-ef14-4117-8e20-b04ff7bcc703
-- title:
--   Repaired V2 Well-Kindedness of Signature Encoding (Theorem 7), Pattern/Spine Elaboration (Theorems 8 & 9), and Kinding-Aware Polarity Classification (Lemmas 3–5)
-- statement:
--   Repaired V2 formulation of Theorem 7 (p. 43), Lemma 3 (p. 43), Theorems 8 & 9 (p. 45), and kinding-aware rigid variable polarity classification (`CheckUse`, Lemmas 4–5, pp. 45–47) in `NishtAbel2024V2`.
--
--   **Differences from the thesis.** Lemmas 4–5 are stated as polarity bounds on kinding-aware size occurrences (`CheckUse`) in a kinding context with unique names, instead of the thesis's four-way classification of rigid variables. This statement replaces the refuted `NishtAbel2024.theorems_7_8_9_and_lemmas_3_4_5`.
-- source:
--   Kanstantsin Nisht, "Type-Based Termination Checking in Agda", Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, TYPES 2024. Repaired V2 formalization.

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Inference

namespace NishtAbel2024V2

/-- Repaired Theorem7 (p. 43), Lemma 3 (p. 43), Theorem 8 (p. 45), Theorem 9 (p. 45),
and Kinding-Aware Rigid Variable Polarity Classification (Lemmas 4–5, pp. 45–47) in `NishtAbel2024V2`:
1. (**Theorem 7**) If `π; Δ ⊢_{SCT}^{π*} A ⇒ Ψ; A'` for `Δ ⊢_{F_ω} A ⇐ *`, then `Δ ⊢ ∀Ψ. A' ⇐ *`.
2. (**Lemma 3**) If `+; Δ ⊢_{SCT}^− A ⇒ Ψ; A'`, then every `i ∈ Ψ` either occurs negatively as a
   `μ`-size variable in `A'` or positively as a `ν`-size variable in `A'` (exclusively).
3. (**Theorem 8**) If `Δ₀ ⊢_{SCT} p : A ⇒ Γ; Δ; Ψ; p'`, then `Δ; Γ ⊢_{Δ₀} p' ⇐ A`.
4. (**Theorem 9**) If `Δ₀ ⊢_{SCT} q⃗ : A ⇒ C; Γ; Δ; Ψ; q⃗'`, then `Δ; Γ | A ⊢_{Δ₀} q⃗' ⇒ C`.
5. (**Repaired Lemma 4**) In any unique-domain kinding context `Δ`, every kinding-aware fixpoint
   occurrence `CheckUse Δ B κ fk i q` of a positively declared pattern rigid variable
   `SizeDecl.mk i .pos a ∈ Δ.sizes` has polarity `q = .pos ∨ q = .top`.
6. (**Repaired Lemma 5**) In any unique-domain kinding context `Δ`, every kinding-aware fixpoint
   occurrence `CheckUse Δ F κ fk i q` of a positively declared rigid variable has
   `q = .pos ∨ q = .top`, and every occurrence of a negatively declared rigid variable has
   `q = .neg ∨ q = .top`. -/
theorem theorems_7_8_9_and_lemmas_3_4_5 :
    (∀ (πstar π : Polarity) (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      SizeCtxWf Δ.sizes →
      FwKindCheck Δ A .star →
      EncodeType πstar π Δ A Ψ A' →
      KindCheck Δ (TypeExpr.forallSizes Ψ A') .star) ∧
    (∀ (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      EncodeType .neg .pos Δ A Ψ A' →
      ∀ i ∈ Ψ.dom,
        (SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A') ∨
        (SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A')) ∧
    (∀ (Δ₀ : KindingCtx) (p p' : Pat) (A : TypeExpr)
       (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferPat Δ₀ p A Γ Δ Ψ p' →
      PatTyping Δ₀ Δ Γ p' A) ∧
    (∀ (Δ₀ : KindingCtx) (qs qs' : PatSpine) (A C : TypeExpr)
       (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferSpine Δ₀ qs A C Γ Δ Ψ qs' →
      SpineTyping Δ₀ Δ Γ A qs' C) ∧
    (∀ (Δ : KindingCtx) (B : TypeExpr) (κ : Kind) (fk : FixKind)
       (i : SizeVar) (q : Polarity) (a : SizeExp),
      Δ.sizes.dom.Nodup →
      SizeDecl.mk i .pos a ∈ Δ.sizes →
      CheckUse Δ B κ fk i q →
      q = .pos ∨ q = .top) ∧
    (∀ (Δ : KindingCtx) (F : TypeExpr) (κ : Kind) (fk : FixKind)
       (i : SizeVar) (q : Polarity) (a : SizeExp),
      Δ.sizes.dom.Nodup →
      ((SizeDecl.mk i .pos a ∈ Δ.sizes → CheckUse Δ F κ fk i q → q = .pos ∨ q = .top) ∧
       (SizeDecl.mk i .neg a ∈ Δ.sizes → CheckUse Δ F κ fk i q → q = .neg ∨ q = .top))) := by
  sorry

end NishtAbel2024V2
