-- Prove2me | Theorems.Thm_NishtAbel2024V5_theorems_2_and_3
-- name    : NishtAbel2024V5.theorems_2_and_3
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T04:17:44.110126+00:00
-- url     : https://prove2.me/theorems/2a0ec0ff-db1d-4786-b6e6-94aac6542d64
-- title:
--   Theorems 2 & 3 (V5): Semantic Soundness of Sizes, Higher-Kinded Kinding, Subtyping, and the Fundamental Reducibility Lemma
-- statement:
--   Establishes the core semantic soundness theorems of System $F_\omega^{\mathsf{cop,SCT}}$ (Chapter 5, Sections 5.3–5.4 of Nisht and Abel 2024):\n\n1. **Theorem 2 — Soundness of Size Judgments**: Let $\Psi$ be a size context and $\rho, \rho^\prime$ be valid ordinal valuations of $\Psi$ satisfying $\rho(i) \le \rho^\prime(i)$ for all $i \in \mathrm{dom}(\Psi)$. Then:\n   $$\Psi \vdash a \implies \llbracket a \rrbracket_\rho \le \llbracket a \rrbracket_{\rho^\prime}, \qquad \Psi \vdash a \le b \implies \llbracket a \rrbracket_\rho \le \llbracket b \rrbracket_{\rho^\prime}, \qquad \Psi \vdash a < b \implies \llbracket a \rrbracket_\rho < \llbracket b \rrbracket_{\rho^\prime}.$$\n2. **Theorem 2 — Soundness of Higher-Kinded Kinding and Polarized Subtyping**: In any closed run-time world $W$, well-formed size context $\Psi$, and valid valuation $\rho$ of $\Psi$, if $\Psi; \cdot \vdash F : \kappa$ then $\llbracket F \rrbracket_\rho \in \mathsf{Good}_\kappa(W)$, and if $\Psi; \cdot \vdash A \le B : \kappa$ then $\mathsf{SemLe}_\kappa(W)(\llbracket A \rrbracket_\rho, \llbracket B \rrbracket_\rho)$.\n3. **Theorem 3 — Fundamental Lemma of Reducibility**: If $W$ is a closed world, $\Sigma = \Omega.\mathsf{sig}$ is semantically valid in $W$, and all local calls into $\Omega.\mathsf{block}$ permitted by $\Omega.\mathsf{localOK}$ are semantically valid at their instantiated size arguments, then every well-typed closed expression $\Omega; \Psi; \cdot; \cdot \vdash t : A$ satisfies $\llbracket t \rrbracket \in \llbracket A \rrbracket_\rho$, and every well-typed copattern clause list $D$ at type $A$ satisfies $\lambda\{D\} \in \llbracket A \rrbracket_\rho$.\n\nThese results form the semantic bridge from syntactic typing and subtyping derivations in $F_\omega^{\mathsf{cop,SCT}}$ to strong normalization via ordinal-indexed reducibility candidates.
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 5, Sections 5.3-5.4, pp. 35-37, Theorems 2-3

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference

namespace NishtAbel2024V5

theorem theorems_2_and_3 :
    (∀ (Ψ : SizeCtx) (ρ ρ' : SizeVal),
      ValidVal Ψ ρ →
      ValidVal Ψ ρ' →
      (∀ i ∈ Ψ.dom, ρ i ≤ ρ' i) →
      (∀ a : Size, SizeWf Ψ a → sizeVal ρ SzEnv.zero a ≤ sizeVal ρ' SzEnv.zero a) ∧
      (∀ a b : Size, SizeLe Ψ a b → sizeVal ρ SzEnv.zero a ≤ sizeVal ρ' SzEnv.zero b) ∧
      (∀ a b : Size, SizeLt Ψ a b → sizeVal ρ SzEnv.zero a < sizeVal ρ' SzEnv.zero b)) ∧
    (∀ (W : World) (Ψ : SizeCtx) (ρ : SizeVal),
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      SizeCtxWf Ψ →
      ValidVal Ψ ρ →
      (∀ (F : Ty) (κ : Kind),
        KindingC Ψ [] F κ →
        Good W κ (interp W ρ TEnv.empty F κ.erase SzEnv.zero Env.empty)) ∧
      (∀ (A B : Ty) (κ : Kind),
        SubTy Ψ [] A B κ →
        SemLe W κ (interp W ρ TEnv.empty A κ.erase SzEnv.zero Env.empty)
          (interp W ρ TEnv.empty B κ.erase SzEnv.zero Env.empty))) ∧
    (∀ (W : World) (Ω : TypingEnv) (Ψ : SizeCtx) (ρ : SizeVal),
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      SemValid W Ω.sig →
      (∀ (Ψ' : SizeCtx) (ρ' : SizeVal) (g : FunDecl) (as : List Size),
        g ∈ Ω.block → Ω.localOK Ψ' g.name as → ValidVal Ψ' ρ' →
        ∀ ρg : SizeVal, ValidVal g.sizeParams ρg →
          g.sizeParams.map (fun p => ρg p.1) = as.map (sizeVal ρ' SzEnv.zero) →
          Tm.fn g.name ∈ interpT W ρg TEnv.empty g.ty SzEnv.zero Env.empty) →
      SizeCtxWf Ψ →
      ValidVal Ψ ρ →
      (∀ (t : Tm) (A : Ty),
        ExprTy Ω Ψ [] [] t A →
        KindingC Ψ [] A .star ∧ t ∈ interpT W ρ TEnv.empty A SzEnv.zero Env.empty) ∧
      (∀ (D : List Clause) (A : Ty),
        KindingC Ψ [] A .star →
        (∀ cl ∈ D, ClauseTy Ω Ψ [] [] cl A) →
        Tm.lam D ∈ interpT W ρ TEnv.empty A SzEnv.zero Env.empty)) := by sorry

end NishtAbel2024V5
