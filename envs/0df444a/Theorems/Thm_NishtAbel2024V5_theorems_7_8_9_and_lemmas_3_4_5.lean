-- Prove2me | Theorems.Thm_NishtAbel2024V5_theorems_7_8_9_and_lemmas_3_4_5
-- name    : NishtAbel2024V5.theorems_7_8_9_and_lemmas_3_4_5
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T04:17:45.01349+00:00
-- url     : https://prove2.me/theorems/0c813074-bded-489e-ac86-5ae4b48033f9
-- title:
--   Theorems 7–9 & Lemmas 3–5 (V5): Signature Encoding, Pattern/Spine Elaboration, and Rigid Variable Polarities
-- statement:
--   Establishes the soundness and polarity invariants of signature encoding and (co)pattern spine elaboration in Chapter 6, Sections 6.1–6.2 (pp. 42–47) of Nisht and Abel (2024):\n\n1. **Theorem 7 — Well-Kindedness of Signature Encoding**: If an unsized type $A$ is well-kinded ($\Delta \vdash A : \kappa$ in `EKinding`) and $\pi; \Delta \vdash_{\mathsf{SCT}}^{\pi^*} A \Rightarrow \Psi; A^\prime$, then $\Psi$ is a well-formed size context (`SizeCtxWf Ψ`) and $\Psi; \Delta \vdash A^\prime : \kappa$.\n2. **Lemma 3 — Exclusive Polarity of Encoded Signature Parameters**: For any signature encoding $+; \Delta \vdash_{\mathsf{SCT}}^- A \Rightarrow \Psi; A^\prime$, every generated size parameter $i \in \mathrm{dom}(\Psi)$ occurs exclusively either negatively as an inductive ($\mu$) size index with $\mathsf{paramPol}(A^\prime, i) = +$ and no $\nu$-occurrences, or positively as a coinductive ($\nu$) size index with $\mathsf{paramPol}(A^\prime, i) = -$ and no $\mu$-occurrences.\n3. **Theorems 8 & 9 — Soundness of Pattern and Copattern Spine Elaboration**: Algorithmic pattern inference `InferPat` implies declarative `PatTy`, and algorithmic copattern spine inference `InferSpine` implies declarative `SpineTy`.\n4. **Lemmas 4 & 5 — Rigid Variable Polarities in Elaborated Contexts**: Every size variable introduced by `InferPat` or `InferSpine` has a rigid (even) name; pattern elaboration introduces only $\mu$-occurrences in the pattern context $\Gamma$; and for an encoded signature type $A$ whose parameters $\mathrm{dom}(\Psi)$ are disjoint from the spine-bound rigid variables $\mathrm{dom}(\Psi^\prime)$, each $i \in \mathrm{dom}(\Psi)$ preserves its exclusive $\mu$-only or $\nu$-only occurrence discipline across both the elaborated term context $\Gamma$ and the residual target type $C$.
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 6, Sections 6.1-6.2, pp. 42-47, Theorems 7-9 & Lemmas 3-5

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference

namespace NishtAbel2024V5

theorem theorems_7_8_9_and_lemmas_3_4_5 :
    (∀ {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx} {A A' : Ty} {Ψ : SizeCtx}
       {κ : Kind},
      EKinding Δ Δb A κ →
      Encode πs ok π Δ Δb A Ψ A' →
      SizeCtxWf Ψ ∧ Kinding Ψ Δ Δb 0 A' κ) ∧
    (∀ {ok : Nat → Prop} {Δ : KCtx} {Δb : BCtx} {A A' : Ty} {Ψ : SizeCtx},
      Encode .neg ok .pos Δ Δb A Ψ A' →
      ∀ i ∈ Ψ.dom,
        (SizeOcc .mu i Δ Δb .neg A' ∧ paramPol A' i = .pos ∧
          (∀ Δ' Δb' q, ¬ SizeOcc .nu i Δ' Δb' q A')) ∨
        (SizeOcc .nu i Δ Δb .pos A' ∧ paramPol A' i = .neg ∧
          (∀ Δ' Δb' q, ¬ SizeOcc .mu i Δ' Δb' q A'))) ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx},
      InferPat Ψ Θ p A Γ Ψ' Θ' →
      PatTy Ψ Θ p A Γ Ψ' Θ') ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
       {Θ' : TyCtx} {C : Ty},
      InferSpine Ψ Θ qs A Γ Ψ' Θ' C →
      SpineTy Ψ Θ qs A Γ Ψ' Θ' C) ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx},
      InferPat Ψ Θ p A Γ Ψ' Θ' →
      (∀ q ∈ Ψ', RigidName q.1) ∧
      (∀ {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol} {xB : Nat × Ty},
        xB ∈ Γ → SizeOcc fk i Δ Δb π xB.2 → A.indexes fk i = true ∨ (fk = .mu ∧ i ∈ Ψ'.dom)) ∧
      (∀ j ∈ Ψ'.dom, A.indexes .nu j = false →
        ∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .nu j Δ Δb π xB.2)) ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
       {Θ' : TyCtx} {C : Ty},
      InferSpine Ψ Θ qs A Γ Ψ' Θ' C →
      (∀ i ∈ Ψ'.dom, RigidName i) ∧
      (∀ {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol},
        ((∃ xB ∈ Γ, SizeOcc fk i Δ Δb π xB.2) ∨ SizeOcc fk i Δ Δb π C) →
        A.indexes fk i = true ∨ i ∈ Ψ'.dom) ∧
      (∀ {ok : Nat → Prop} {Δ₀ : KCtx} {Δb₀ : BCtx} {A₀ : Ty},
        Encode .neg ok .pos Δ₀ Δb₀ A₀ Ψ A →
        NamesDisjoint Ψ.dom Ψ'.dom →
        ∀ i ∈ Ψ.dom,
          (paramPol A i = .pos ∧
            (∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .nu i Δ Δb π xB.2) ∧
            (∀ Δ Δb π, ¬ SizeOcc .nu i Δ Δb π C)) ∨
          (paramPol A i = .neg ∧
            (∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .mu i Δ Δb π xB.2) ∧
            (∀ Δ Δb π, ¬ SizeOcc .mu i Δ Δb π C)))) := by sorry

end NishtAbel2024V5
