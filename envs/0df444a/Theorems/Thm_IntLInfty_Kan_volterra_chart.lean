-- Prove2me | Theorems.Thm_IntLInfty_Kan_volterra_chart
-- name    : IntLInfty.Kan.volterra_chart
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:13:28.925283+00:00
-- url     : https://prove2.me/theorems/05a1dcab-1e3c-4f54-86e8-0546935941a4
-- title:
--   The Volterra chart $G,H$ of $\int_S$
-- statement:
--   There are maps $G_S:\mathrm{Amb}\to\mathrm{Amb}$ and continuous linear $H_S$ such that for every $\delta$-closed $S$: $G_S(z)_{t,k}$ is the jet of the cone integral $K\varphi(\delta b_{t,k})$ for any DGA lift $\varphi$ of $z$, $G_S$ is smooth, $H_S$ is an idempotent fixing $G_S$, $$z\in\int_S\iff H_S(z-G_S z)=0,$$ and $G,H$ commute with the faces $d_i$ ($i\ne0$) and with restriction to $S'\le S$.
--
--   Role: the chart of the proof of Theorem 5.10 in which integrality becomes the zero set of $H(z-G z)$.
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

theorem volterra_chart (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) :
    ∃ (G : ∀ (S : GenSys L) (m : ℕ), Amb r S m → Amb r S m)
      (H : ∀ (S : GenSys L) (m : ℕ), Amb r S m →L[ℝ] Amb r S m),
    ∀ S : GenSys L, (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S) →
      (∀ (m : ℕ) (z : Amb r S m) (φ : CE L →ₐ[ℝ] Ω m),
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ))) →
      (∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        jet r (φ (gen L t (genBasis S t k))) = (z t k : Jet r m × Jet r m)) →
      ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        (G S m z t k : Jet r m × Jet r m) = jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff (φ (δ.δ (gen L t (genBasis S t k)))) I (s • y)) •
                formBasis m I))) ∧
      (∀ m, CompleteSpace (Amb r S m)) ∧
      (∀ m, ContDiff ℝ ∞ (G S m)) ∧
      (∀ m z, H S m (H S m z) = H S m z) ∧
      (∀ m z, H S m (G S m z) = G S m z) ∧
      (∀ m z v, H S m (fderiv ℝ (G S m) z v) = fderiv ℝ (G S m) z v) ∧
      (∀ m z, z ∈ integ r δ S m ↔ H S m (z - G S m z) = 0) ∧
      (∀ m (i : Fin (m + 2)), i ≠ 0 → ∀ z,
        faceAmb r S m i (G S (m + 1) z) = G S m (faceAmb r S m i z)) ∧
      (∀ m (i : Fin (m + 2)), i ≠ 0 → ∀ z,
        faceAmb r S m i (H S (m + 1) z) = H S m (faceAmb r S m i z)) ∧
      ((∀ t, 0 < t → Module.finrank ℝ (S t) = 0) → ∀ m z v, H S m v = v →
        G S m (z + v) = G S m z + fderiv ℝ (G S m) z v) ∧
      (∀ (S' : GenSys L) (h : ∀ i, S' i ≤ S i), (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S' i → δ.δ (gen L i ξ) ∈ genAlg L S') →
        ∀ m z, res h (G S m z) = G S' m (res h z) ∧ res h (H S m z) = H S' m (res h z)) := by sorry

end IntLInfty.Kan
