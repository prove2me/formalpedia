-- Prove2me | Theorems.Thm_NishtAbel2024V5_theorems_10_11_and_12
-- name    : NishtAbel2024V5.theorems_10_11_and_12
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T04:17:49.247044+00:00
-- url     : https://prove2.me/theorems/eebcee21-ac49-4d2a-ae5c-691c4eabfc66
-- title:
--   Theorems 10, 11 & 12 (V5): Constraint Orientation in Subtype Comparison and Call-Site Inference
-- statement:
--   Characterizes the structure and variable provenance of all size constraints emitted during algorithmic subtype comparison and bidirectional call-site checking (Chapter 6, Section 6.3, pp. 52–56 of Nisht and Abel 2024):\n\n1. **Theorem 10 — Constraints in Higher-Kinded Type Comparison**: Every constraint $c \in C$ emitted by $\Psi; \Delta \vdash A \le B : \kappa \Rightarrow C$ (`Compare Ψ Δ A B κ C`) is a non-strict, upper-bound-normalized inequality ($c.\mathsf{strict} = \mathsf{false}$, $c.\mathsf{up} = \mathsf{true}$) in context $c.\mathsf{ctx} = \Psi$ whose free size variables $\mathsf{fvars}(c.\mathsf{lhs}) \cup \mathsf{fvars}(c.\mathsf{rhs})$ are either all $\mu$-indices of $A$ or $B$, or all $\nu$-indices of $A$ or $B$:\n   $$\forall c \in C,\quad (\forall i \in \mathsf{fvars}(c),\; i \in \mathsf{idx}_\mu(A) \cup \mathsf{idx}_\mu(B)) \;\vee\; (\forall i \in \mathsf{fvars}(c),\; i \in \mathsf{idx}_\nu(A) \cup \mathsf{idx}_\nu(B)).$$\n2. **Theorems 11 & 12 — Constraints in Expression Inference, Checking, and Clause Checking**: Every constraint $c \in C$ emitted by `InferTm`, `CheckTm`, or `CheckClause` belongs to one of three classes:\n   - a strict constructor or projection step constraint $j < a^\uparrow$ where $j$ is a flexible variable recorded in $\Phi$ with polarity $\pi \in \{+, -\}$;\n   - a strict recursive call-bound constraint $k < b[\vec{a}/\Psi_g]$ where $k$ is a flexible variable; or\n   - a non-strict comparison constraint arising from `Compare` whose variables are pure $\mu$-indices or pure $\nu$-indices of the compared types.
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 6, Section 6.3, pp. 52-56, Theorems 10-12

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference

namespace NishtAbel2024V5

theorem theorems_10_11_and_12 :
    (∀ {Ψ : SizeCtx} {Δ : KCtx} {A B : Ty} {κ : Kind} {C : List SConstr},
      Compare Ψ Δ A B κ C →
      ∀ c ∈ C,
        c.ctx = Ψ ∧ c.strict = false ∧ c.up = true ∧
        ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars, A.indexes .mu i = true ∨ B.indexes .mu i = true) ∨
         (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars, A.indexes .nu i = true ∨ B.indexes .nu i = true))) ∧
    (∀ {Ω : InfEnv},
      (∀ {Ψ Θ Γ r A Φ C T K},
        InferTm Ω Ψ Θ Γ r A Φ C T K →
        ∀ c ∈ C,
          (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
            c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
          (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
          (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
            ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
             (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true)))) ∧
      (∀ {Ψ Θ Γ A t Φ C T K},
        CheckTm Ω Ψ Θ Γ A t Φ C T K →
        ∀ c ∈ C,
          (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
            c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
          (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
          (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
            ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
             (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true)))) ∧
      (∀ {Ψ Θ Γ A cl Φ C T K},
        CheckClause Ω Ψ Θ Γ A cl Φ C T K →
        ∀ c ∈ C,
          (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
            c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
          (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
          (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
            ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
             (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true))))) := by sorry

end NishtAbel2024V5
