-- Prove2me | Theorems.Thm_IntLInfty_Kan_fillers_horn_transport
-- name    : IntLInfty.Kan.fillers_horn_transport
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:10:51.432118+00:00
-- url     : https://prove2.me/theorems/51c50144-b169-44fe-bd7b-0920dac1c715
-- title:
--   Transport of horn fillers from horn $0$ to horn $j$
-- statement:
--   If $\int_S\to\int_{S'}$ has a smooth relative filler family for $\Lambda[m+1,0]$, it has one for every $\Lambda[m+1,j]$: $$\exists\sigma_0\implies\exists\sigma_j.$$
--
--   Role: the vertex-swap symmetry reducing all horns to horn 0.
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

theorem fillers_horn_transport (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (S S' : GenSys L)
    (h : ∀ i, S' i ≤ S i) (m : ℕ) (j : Fin (m + 2))
    (h0 : ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)) →
        Amb r S (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m 0,
          σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m 0 (σ x y) = y) ∧
      (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m 0 x) = x)) :
    ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) →
        Amb r S (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m j,
          σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m j (σ x y) = y) ∧
      (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m j x) = x) := by sorry

end IntLInfty.Kan
