-- Prove2me | Theorems.Thm_NishtAbel2024_theorem2_size_soundness
-- name    : NishtAbel2024.theorem2_size_soundness
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T21:31:51.646524+00:00
-- url     : https://prove2.me/theorems/2be04c88-c741-41b3-b037-3b37248768bc
-- title:
--   Semantic soundness of size judgments in the current model
-- statement:
--   For a well-formed size context Ψ and valuations ρ, ρ′ related by SizeValLe Ψ, every well-formed size expression evaluates monotonically from ρ to ρ′. If Ψ derives a ≤ b, the evaluation of a at ρ is at most that of b at ρ′; if Ψ derives a < b, the corresponding inequality is strict. This is exactly the first conjunct of the original formal Theorems 2–3 statement, using its existing NishtAbel2024 syntax and lexicographic Nat × Nat semantic model. It does not prove expression or clause soundness. The current size model has order type ω², unlike the ordinal universe described in the thesis.
-- source:
--   Kanstantsin Nisht, Type-Based Termination Checking in Agda, master's thesis supervised by Andreas Abel (2024), https://knisht.github.io/agda/msc.pdf, Theorem 2, Section 5.4.1, p. 36. This is the exact size conjunct of the existing Lean formalization, whose SizeOrd model is Nat × Nat in lexicographic order (ω²), not the source's first uncountable ordinal interpretation.

import Definitions.Def_NishtAbel2024_Syntax
import Definitions.Def_NishtAbel2024_Semantics

namespace NishtAbel2024

/-- The exact size-soundness conjunct of the existing Theorems 2–3 statement.
This result concerns the current `SizeOrd` and size-judgment definitions. -/
theorem theorem2_size_soundness :
    ∀ (Ψ : SizeCtx) (ρ ρ' : SizeVal),
      SizeCtxWf Ψ →
      SizeValLe Ψ ρ ρ' →
      (∀ a : SizeExp, SizeWf Ψ a → SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' a)) ∧
      (∀ a b : SizeExp, SizeLe Ψ a b → SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' b)) ∧
      (∀ a b : SizeExp, SizeLt Ψ a b → SizeOrd.lt (evalSizeExp ρ a) (evalSizeExp ρ' b)) := by
  sorry

end NishtAbel2024
