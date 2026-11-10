-- Prove2me | Theorems.Thm_IntLInfty_Kan_isKanFibration_of_fillers
-- name    : IntLInfty.Kan.isKanFibration_of_fillers
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T02:10:59.152221+00:00
-- url     : https://prove2.me/theorems/3a3238e8-3755-44bf-90b1-12c56adddbd8
-- title:
--   Kan fibration from smooth horn fillers
-- statement:
--   If $S'\le S$, all levels of $\int_S$ and $\int_{S'}$ are split submanifolds, and for all $m,j$ there is a smooth family $\sigma$ of relative horn fillers ($\sigma(x,y)\in\int_S$, $\mathrm{kan}(\sigma(x,y))=y$, $\sigma(x,\mathrm{kan}\,x)=x$), then $$\int_S\to\int_{S'}\ \text{is a Kan fibration}.$$
--
--   Role: turns the filler families of the proof into the Kan-fibration statement (Definition 2.3).
-- source:
--   Henriques, Integrating L-infinity algebras, Compositio Math. 144 (2008), arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, proof of Theorem 5.10 (Section 5, pp. 15-17)

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

set_option autoImplicit false

open scoped ContDiff

namespace IntLInfty.Kan

theorem isKanFibration_of_fillers (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (S S' : GenSys L)
    (h : ∀ i, S' i ≤ S i)
    (hS : ∀ m, IsSplitSubmanifold (integ r δ S m)) (hS' : ∀ m, IsSplitSubmanifold (integ r δ S' m))
    (hF : ∀ (m : ℕ) (j : Fin (m + 2)),
      ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) →
          Amb r S (m + 1),
        (∀ x, ContDiff ℝ ∞ (σ x)) ∧
        (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m j,
            σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m j (σ x y) = y) ∧
        (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m j x) = x)) :
    IsKanFibration r δ S S' := by sorry

end IntLInfty.Kan
