-- Prove2me | Theorems.Thm_LIPAlgorithm_theorem_5_14
-- name    : LIPAlgorithm.theorem_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:42.715591+00:00
-- url     : https://prove2.me/theorems/3531193e-77bd-4dc5-8377-94033a59b98a
-- title:
--   Theorem 5.14 — small-rank residual-glue canonical forms
-- statement:
--   There is a function $\mathrm{Can}$ on residual-glue instances and deterministic machines $M_1,M_2$ such that, for valid instances of residual rank $r$ and encoding length $\ell$, $M_1$ computes $\mathrm{Can}(\mathcal G)$, and on two instances with equal canonical strings $M_2$ outputs a duplicate-free list of exactly the residual-glue isomorphisms, both within $(r+2)^{C(r+2)}(\ell+1)^K$ steps. Moreover,
--
--   $$\mathrm{Can}(\mathcal G_1)=\mathrm{Can}(\mathcal G_2)\iff\text{there is a residual-glue isomorphism }\mathcal G_1\to\mathcal G_2.$$
--
--   Each label and each lift of the main algorithm reduces to this primitive.
--
--   Differences from the source:
--   - reading: a deterministic algorithm, in an unnamed machine model → one Mathlib TM2 machine, with runs counted per input (Turing.TM2OutputsInTime); reason: the paper names no model; TM2 is the strongest standard reading, and every step of the routine costs r^{O(r)} times a polynomial, a class closed under the polynomial overhead of simulating it on stacks, so the bound survives
--   - encoding: time r^{O(r)} plus output → (r+2)^{C(r+2)}·(ℓ+1)^K, with the output inside; reason: as in Theorem 5.12; the output has at most Baut(r) matrices of polynomial bit length
--   - reading: equal strings characterize isomorphism, stated in the proof and the 'Target primitive', p.25 → an explicit iff clause, with equal strings forcing equal d, r; reason: this is the property the paper uses, and it is printed there
--   - generalization: instances in the primitive integral model → instances with integral K_H, primitive or not; reason: the construction never uses primitivity; primitive instances are a subclass
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Theorem 5.14, p.29; Target primitive, p.25

import Mathlib
import Definitions.Def_LIPAlgorithm_ResGlue
import Definitions.Def_LIPAlgorithm_RunsWithin

namespace LIPAlgorithm

/-- **Theorem 5.14 (Small-rank residual-glue canonical forms).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256
61ee52aa…), Theorem 5.14, p.29 (PDF p.32), with the "Target primitive" paragraph, p.25.

There is a function `Can` and deterministic machines `M₁`, `M₂` such that `M₁` computes `Can(G)` and, on two instances with equal
strings, `M₂` outputs a duplicate-free list of exactly the residual-glue isomorphisms, both within `(r+2)^{C(r+2)}·(ℓ+1)^K` steps;
and equal strings occur exactly when an isomorphism exists.

**Formalization Note.** `(r+2)`, `(ℓ+1)^K` and "plus output" are as in `theorem_5_12`. Equal strings force equal `d` and `r`, stated as
its own clause, since isomorphisms are between instances of the same shape. -/
theorem theorem_5_14 :
    ∃ (Can : ∀ d r : ℕ, ResGlue d r → List Bool) (M₁ M₂ : Turing.TM2ComputableAux Bool Bool) (C K : ℕ),
      (∀ (d r : ℕ) (G : ResGlue d r), G.IsValid →
        RunsWithin M₁ (encResGlue G) (Can d r G)
          ((r + 2) ^ (C * (r + 2)) * ((encResGlue G).length + 1) ^ K)) ∧
      (∀ (d₁ r₁ d₂ r₂ : ℕ) (G₁ : ResGlue d₁ r₁) (G₂ : ResGlue d₂ r₂), G₁.IsValid → G₂.IsValid →
        Can d₁ r₁ G₁ = Can d₂ r₂ G₂ → d₁ = d₂ ∧ r₁ = r₂) ∧
      (∀ (d r : ℕ) (G₁ G₂ : ResGlue d r), G₁.IsValid → G₂.IsValid →
        (Can d r G₁ = Can d r G₂ ↔ ∃ U, IsResGlueIso G₁ G₂ U)) ∧
      (∀ (d r : ℕ) (G₁ G₂ : ResGlue d r), G₁.IsValid → G₂.IsValid → Can d r G₁ = Can d r G₂ →
        ∃ Us : List (Gram r), Us.Nodup ∧ (∀ U, U ∈ Us ↔ IsResGlueIso G₁ G₂ U) ∧
          RunsWithin M₂ (encResGlue G₁ ++ encResGlue G₂) (encMatList Us)
            ((r + 2) ^ (C * (r + 2)) * ((encResGlue G₁ ++ encResGlue G₂).length + 1) ^ K)) := by sorry

end LIPAlgorithm
