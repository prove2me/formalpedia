-- Prove2me | Theorems.Thm_NishtAbel2024V5_theorems_13_and_14
-- name    : NishtAbel2024V5.theorems_13_and_14
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T04:17:39.215818+00:00
-- url     : https://prove2.me/theorems/62fa83a5-4d72-42f5-9c6f-93550d5e0e52
-- title:
--   Theorems 13 & 14 and Corollary (V5): Soundness of Coherent Substitutions, Algorithm 1 Solver, and Algorithm 2 Typing
-- statement:
--   Proves that coherent, scope-respecting solutions to the inference constraints elaborate source clauses into well-typed target derivations in System $F_\omega^{\mathsf{cop,SCT}}$ (Chapter 6, Sections 6.3–6.5, pp. 56–59 of Nisht and Abel 2024):\n\n1. **Theorem 13 — Soundness of Call-Site Inference under Coherent Substitutions**: Let $\varphi$ be a flexible substitution (`∀ p ∈ φ, FlexName p.1`) that is coherent for $C$ (`Coherent φ C`) and respects the rigid scopes recorded in $\Phi$ (`ScopeOK φ Φ`). If `CheckClause Ω Ψ Θ Γ A cl Φ C T K` holds and every call record $k \in K$ satisfies $\Omega_d.\mathsf{localOK}(k.\mathsf{ctx}[\varphi], k.\mathsf{callee}, k.\mathsf{args}[\varphi])$, then applying $\varphi$ yields a declarative clause typing derivation:\n   $$\Omega_d;\; \Psi[\varphi];\; \Theta;\; \Gamma[\varphi] \vdash cl : A[\varphi].$$\n2. **Theorem 14 — Soundness of Checked Algorithm 1 Constraint Solving**: Whenever the closed-form solver $\varphi = \mathsf{solve}(\mathsf{fuel}, \Phi, C, T)$ passes the decidable scope and coherence checks (`checkScope φ Φ = true` and `checkCoherent fuel φ C = true`), $\varphi$ has flexible domain and satisfies `ScopeOK φ Φ` and `Coherent φ C`.\n3. **Corollary — Mutual Blocks Accepted by Algorithm 2 Are Well-Typed**: If all global signature declarations in $\Sigma$ are well-kinded and `Algorithm2Accepts sig Ξ Ξannot` holds, then the size-annotated mutual block $\Xi_{\mathsf{annot}}$ is well-typed in System $F_\omega^{\mathsf{cop,SCT}}$ (`BlockTy sig Ξannot`).
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 6, Sections 6.3-6.5, pp. 56-59, Theorems 13-14 & Corollary

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference

namespace NishtAbel2024V5

theorem theorems_13_and_14 :
    (∀ {Ω : InfEnv} {Ωd : TypingEnv} {φ : FlexSubst}
       {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {A : Ty} {cl : Clause}
       {Φ : List FlexVar} {C : List SConstr} {T : List Nat} {K : List CallRec},
      Ω.sig = Ωd.sig →
      Ω.block = Ωd.block →
      (∀ g ∈ Ω.sig, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star) →
      (∀ g ∈ Ω.block, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star) →
      (∀ p ∈ φ, FlexName p.1) →
      CheckClause Ω Ψ Θ Γ A cl Φ C T K →
      Coherent φ C →
      ScopeOK φ Φ →
      (∀ k ∈ K, Ωd.localOK (k.ctx.substBounds φ) k.callee (k.args.map (Size.subst φ))) →
      (∀ p ∈ Γ, KindingC (Ψ.substBounds φ) Θ.toK (p.2.substSize φ) .star) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
      ClauseTy Ωd (Ψ.substBounds φ) Θ (Γ.map fun p => (p.1, p.2.substSize φ)) cl
        (A.substSize φ)) ∧
    (∀ (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat),
      (∀ v ∈ Φ, FlexName v.name) →
      checkScope (solve fuel Φ C T) Φ = true →
      checkCoherent fuel (solve fuel Φ C T) C = true →
      (∀ p ∈ solve fuel Φ C T, FlexName p.1) ∧
        ScopeOK (solve fuel Φ C T) Φ ∧
        Coherent (solve fuel Φ C T) C) ∧
    (∀ {sig Ξ Ξannot : List FunDecl},
      (∀ g ∈ sig, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star) →
      Algorithm2Accepts sig Ξ Ξannot →
      BlockTy sig Ξannot) := by sorry

end NishtAbel2024V5
