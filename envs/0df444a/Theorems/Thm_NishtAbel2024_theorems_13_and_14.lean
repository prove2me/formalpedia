-- Prove2me | Theorems.Thm_NishtAbel2024_theorems_13_and_14
-- name    : NishtAbel2024.theorems_13_and_14
-- status  : Disproved
-- author  : @kmehltretter82
-- created : 2026-10-31T19:06:54.411874+00:00
-- url     : https://prove2.me/theorems/c6d32b44-f24c-47eb-b53c-08f3b9d07821
-- title:
--   Typing Soundness of Coherent Flexible Substitutions (Theorem 13) and Coherence of Algorithm 1 (Theorem 14 & Corollary)
-- statement:
--   Theorems 13, 14, and Corollary (Section 6.4, pp. 56–58): (1) any coherent flexible substitution `CoherentSubst (Ψ₁ ++ Ψ₂) Cs φ` whose call sites satisfy `LocalCallsConform` turns the elaborated term `t'.applyFlex φ` into a well-typed System `F_ω^{cop, SCT}` expression (`ExprCheck`); (2) the substitution `φ* := solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T` computed by Algorithm 1 is coherent; and (3) consequently `t'.applyFlex φ*` is well-typed in System `F_ω^{cop, SCT}`.
-- source:
--   Kanstantsin Nisht, 'Type-Based Termination Checking in Agda', Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, 30th International Conference on Types for Proofs and Programs (TYPES 2024). Section 6.4, Theorem 13 (p. 56), Theorem 14 (p. 58), and Corollary (p. 58).

import Definitions.Def_NishtAbel2024_Syntax
import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024

/-- Theorem 13 (Soundness of coherent substitutions, pp. 56–57),
Theorem 14 (Soundness of `φ*`, p. 58), and
Corollary (Correctness of Algorithm 1, p. 58):
1. (**Theorem 13**) Any coherent flexible substitution `φ` (`CoherentSubst (Ψ₁ ++ Ψ₂) Cs φ`)
   satisfying `LocalCallsConform` turns the size-inferred term `t'` into a well-typed System
   `F_ω^{cop, SCT}` term `ExprCheck ⟨sig, Ξ, 𝒢, f, Ψ₁⟩ ((Δ₀.extSizes Ψ₁).extDecls Δ) Γ (t'.applyFlex φ) C`.
2. (**Theorem 14**) Under the conditions of Theorem 12, the substitution
   `φ* := solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T` computed by Algorithm 1 satisfies
   `CoherentSubst (Ψ₁ ++ Ψ₂) Cs φ*`.
3. (**Corollary**) Combining Theorems 13 and 14, when `φ*(t')` satisfies `LocalCallsConform`,
   `φ*(t')` is well-typed in System `F_ω^{cop, SCT}`. -/
theorem theorems_13_and_14 :
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (𝒢 : InvGraphFamily) (f : FunName)
       (Δ₀ : KindingCtx) (Ψ₁ Ψ₂ : SizeCtx) (A A₀ C : TypeExpr)
       (qs qs' : PatSpine) (Γ : TermCtx) (Δ : List TyDecl)
       (t t' : Term) (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar)
       (φ : FlexSubst),
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ C Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) C t Φ Cs T t' →
      CoherentSubst (Ψ₁ ++ Ψ₂) Cs φ →
      LocalCallsConform Ξ 𝒢 f Ψ₁ (Ψ₁ ++ Ψ₂) (t'.applyFlex φ) →
      ExprCheck ⟨sig, Ξ, 𝒢, f, Ψ₁⟩ ((Δ₀.extSizes Ψ₁).extDecls Δ) Γ (t'.applyFlex φ) C) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (Δ₀ : KindingCtx)
       (Ψ₁ Ψ₂ : SizeCtx) (A A₀ A'' : TypeExpr) (qs qs' : PatSpine)
       (Γ : TermCtx) (Δ : List TyDecl) (t t' : Term)
       (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar),
      SizeCtxWf (Ψ₁ ++ Ψ₂) →
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) A'' t Φ Cs T t' →
      CoherentSubst (Ψ₁ ++ Ψ₂) Cs (solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (𝒢 : InvGraphFamily) (f : FunName)
       (Δ₀ : KindingCtx) (Ψ₁ Ψ₂ : SizeCtx) (A A₀ C : TypeExpr)
       (qs qs' : PatSpine) (Γ : TermCtx) (Δ : List TyDecl)
       (t t' : Term) (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar),
      let φstar := solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T
      SizeCtxWf (Ψ₁ ++ Ψ₂) →
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ C Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) C t Φ Cs T t' →
      LocalCallsConform Ξ 𝒢 f Ψ₁ (Ψ₁ ++ Ψ₂) (t'.applyFlex φstar) →
      ExprCheck ⟨sig, Ξ, 𝒢, f, Ψ₁⟩ ((Δ₀.extSizes Ψ₁).extDecls Δ) Γ (t'.applyFlex φstar) C) := by
  sorry

end NishtAbel2024
