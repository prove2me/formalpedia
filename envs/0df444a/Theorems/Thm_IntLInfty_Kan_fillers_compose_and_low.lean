-- Prove2me | Theorems.Thm_IntLInfty_Kan_fillers_compose_and_low
-- name    : IntLInfty.Kan.fillers_compose_and_low
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T02:11:10.310938+00:00
-- url     : https://prove2.me/theorems/ca4acb28-ad47-4ade-970d-3b3a7a31fd83
-- title:
--   Smooth horn fillers compose; fillers when $S,S'$ agree below $m+1$
-- statement:
--   (i) Smooth relative horn filler families for $\int_S\to\int_{S'}$ and $\int_{S'}\to\int_{S''}$ give one for $\int_S\to\int_{S''}$; (ii) if $S_i\le S'_i$ for $i\le m$ and both are $\delta$-closed, there is a smooth filler family at level $m$: $$S_{\le m}=S'_{\le m}\implies \exists\sigma\ \text{filling}\ \Lambda[m+1,j].$$
--
--   Role: composition along the Postnikov tower and the low-degree case used for $\int L\to *$.
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

theorem fillers_compose_and_low (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) :
    (∀ (S S' S'' : GenSys L) (h1 : ∀ i, S' i ≤ S i) (h2 : ∀ i, S'' i ≤ S' i) (h3 : ∀ i, S'' i ≤ S i)
      (m : ℕ) (j : Fin (m + 2)),
      (∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) →
          Amb r S (m + 1),
        (∀ x, ContDiff ℝ ∞ (σ x)) ∧
        (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h1 m j,
            σ x y ∈ integ r δ S (m + 1) ∧ kanMap h1 m j (σ x y) = y) ∧
        (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h1 m j x) = x)) →
      (∃ σ : Amb r S' (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S' m) × Amb r S'' (m + 1)) →
          Amb r S' (m + 1),
        (∀ x, ContDiff ℝ ∞ (σ x)) ∧
        (∀ x ∈ integ r δ S' (m + 1), ∀ y ∈ RelHorn r δ h2 m j,
            σ x y ∈ integ r δ S' (m + 1) ∧ kanMap h2 m j (σ x y) = y) ∧
        (∀ x ∈ integ r δ S' (m + 1), σ x (kanMap h2 m j x) = x)) →
      ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S'' (m + 1)) →
          Amb r S (m + 1),
        (∀ x, ContDiff ℝ ∞ (σ x)) ∧
        (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h3 m j,
            σ x y ∈ integ r δ S (m + 1) ∧ kanMap h3 m j (σ x y) = y) ∧
        (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h3 m j x) = x)) ∧
    (∀ (S S' : GenSys L) (h : ∀ i, S' i ≤ S i) (m : ℕ), (∀ i, i < m + 1 → S i ≤ S' i) →
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S) →
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S' i → δ.δ (gen L i ξ) ∈ genAlg L S') →
      ∀ j : Fin (m + 2),
      ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) →
          Amb r S (m + 1),
        (∀ x, ContDiff ℝ ∞ (σ x)) ∧
        (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m j,
            σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m j (σ x y) = y) ∧
        (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m j x) = x)) := by sorry

end IntLInfty.Kan
