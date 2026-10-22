-- Prove2me | Theorems.Thm_NewtonCartan_exists_potential_of_closed_hessian_Sp
-- name    : NewtonCartan.exists_potential_of_closed_hessian_Sp
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:52:05.243016+00:00
-- url     : https://prove2.me/theorems/0ed8c69f-7848-478b-b3fc-ba6785dfd0cb
-- title:
--   Potential for a closed symmetric Hessian on $\mathbb{R}^3$
-- statement:
--   Let $H:\mathbb{R}^3\to\mathrm{Sym}^2(\mathbb{R}^3)$ be a $C^\infty$ field of symmetric matrices that is closed as a Hessian, i.e.
--   $$
--   \partial_k H_{ij}=\partial_j H_{ik}\qquad\text{for all spatial indices }i,j,k.
--   $$
--   Then there exists a $C^\infty$ potential $\varphi:\mathbb{R}^3\to\mathbb{R}$ with
--   $$
--   \partial_j\partial_i\varphi = H_{ij}.
--   $$
--   The proof applies the ContDiff Poincaré lemma twice: first to each row of $H$ (producing a closed $1$-form $A$), then to $A$ (producing $\varphi$). This is the constant-$t$ slice of the Trautman recovery Poincaré step in Malament/Weatherall Proposition 2.2.
--
--   Formalization Note. Uses `NewtonCartan.contDiff_primitive_of_closed_oneForm`. Child of `exists_potential_of_spatial_F`.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Theorems.Thm_NewtonCartan_contDiff_primitive_of_closed_oneForm

open scoped ContDiff Topology
open Classical

namespace NewtonCartan

abbrev Sp := Fin 3 → ℝ

theorem exists_potential_of_closed_hessian_Sp
    (H : Sp → Fin 3 → Fin 3 → ℝ) (hH : ContDiff ℝ ∞ H)
    (hsym : ∀ y i j, H y i j = H y j i)
    (hclosed : ∀ y i j k,
      fderiv ℝ (fun z => H z i j) y (Pi.single k 1) =
        fderiv ℝ (fun z => H z i k) y (Pi.single j 1)) :
    ∃ φ : Sp → ℝ, ContDiff ℝ ∞ φ ∧
      ∀ y i j, fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single i 1)) y (Pi.single j 1) =
        H y i j := by sorry

end NewtonCartan
