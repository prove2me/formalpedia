-- Prove2me | Theorems.Thm_IntLInfty_Kan_tauLe_gmap_fibre_affine
-- name    : IntLInfty.Kan.tauLe_gmap_fibre_affine
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:13:20.879197+00:00
-- url     : https://prove2.me/theorems/9a59425d-b36f-4b11-a3bd-510409ef776d
-- title:
--   $G$ is affine along the fibres of $\int\tau_{\le n}\to\int\tau_{<n}$, $n\ge1$
-- statement:
--   For $n\ge1$ and the chart map $G$ of $\int\tau_{\le n}$: if $\mathrm{res}\,v=0$ then $$G(z+v)=G(z)+DG_z(v).$$
--
--   Role: the fibre-affinity hypothesis of the abstract horn-0 filler for $n\ge1$.
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

theorem tauLe_gmap_fibre_affine (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ i, tauLt δ n i ≤ tauLe δ n i)
    (G : ∀ m, Amb r (tauLe δ n) m → Amb r (tauLe δ n) m)
    (hG : (∀ (m : ℕ) (z : Amb r (tauLe δ n) m) (φ : CE L →ₐ[ℝ] Ω m),
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ (tauLe δ n) i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ))) →
      (∀ (t : Fin m) (k : Fin (Module.finrank ℝ ((tauLe δ n) t))),
        jet r (φ (gen L t (genBasis (tauLe δ n) t k))) = (z t k : Jet r m × Jet r m)) →
      ∀ (t : Fin m) (k : Fin (Module.finrank ℝ ((tauLe δ n) t))),
        (G m z t k : Jet r m × Jet r m) = jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff (φ (δ.δ (gen L t (genBasis (tauLe δ n) t k)))) I (s • y)) •
                formBasis m I))))
    (hGc : ∀ m, ContDiff ℝ ∞ (G m)) (m : ℕ) (z v : Amb r (tauLe δ n) m) (hv : res h v = 0) :
    G m (z + v) = G m z + fderiv ℝ (G m) z v := by sorry

end IntLInfty.Kan
