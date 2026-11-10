-- Prove2me | Theorems.Thm_IntLInfty_Kan_volterra_chart_contraction
-- name    : IntLInfty.Kan.volterra_chart_contraction
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:13:21.516256+00:00
-- url     : https://prove2.me/theorems/28db8b58-949c-4cbf-af4c-028e50a58388
-- title:
--   Volterra contraction for the chart map $G$
-- statement:
--   If $G$ is the chart map of $\int_S$ (characterised by the cone integral of DGA lifts) and smooth, then at every point $x$ some power of its derivative is a strict contraction: $$\exists n,\ \|(DG_x)^n\|<1.$$
--
--   Role: the Volterra estimate (the derivative of $G$ is a Volterra-type operator) used for split submanifolds and fibre inverses.
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

theorem volterra_chart_contraction (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (S : GenSys L)
    (hcl : (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S))
    (G : ∀ m, Amb r S m → Amb r S m)
    (hG : (∀ (m : ℕ) (z : Amb r S m) (φ : CE L →ₐ[ℝ] Ω m),
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ))) →
      (∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        jet r (φ (gen L t (genBasis S t k))) = (z t k : Jet r m × Jet r m)) →
      ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        (G m z t k : Jet r m × Jet r m) = jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff (φ (δ.δ (gen L t (genBasis S t k)))) I (s • y)) •
                formBasis m I))))
    (hGc : ∀ m, ContDiff ℝ ∞ (G m)) (m : ℕ) (x : Amb r S m) :
    ∃ n : ℕ, ‖(fderiv ℝ (G m) x) ^ n‖ < 1 := by sorry

end IntLInfty.Kan
