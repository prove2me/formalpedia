-- Prove2me | Theorems.Thm_Module_length_quotient_torsionBySet_sup_eq_iff
-- name    : Module.length_quotient_torsionBySet_sup_eq_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/2645367e-4537-568c-b8ca-bf28691426b2
-- title:
--   Equality in the congruence-module bound iff M[wp]=I· M
-- statement:
--   Let $\mathcal O$ be a commutative domain that is a principal ideal ring, let $T$ be a commutative $\mathcal O$-algebra which is free as an $\mathcal O$-module, and let $\pi_T : T \to \mathcal O$ be an $\mathcal O$-algebra homomorphism. Write $\wp = \ker \pi_T$, let $I = \wp^{\perp}$ be the annihilator ideal of $\wp$ in $T$, and assume that the ideal $\eta = \pi_T(I)$ of $\mathcal O$, i.e. the image of $I$ under $\pi_T$, is nonzero. Let $M$ be an abelian group carrying a $T$-module structure and an $\mathcal O$-module structure, compatible in the sense that $\mathcal O$ acts through $T$, and suppose $M$ is finite and free as an $\mathcal O$-module. Denote by $M[\wp]$ and $M[I]$ the submodules of elements annihilated by every element of $\wp$, resp. of $I$. The assertion is the equivalence of the following two statements: first, the $\mathcal O$-length of $M/(M[\wp] + M[I])$ equals the product, computed in $\mathbb N_\infty$, of $\operatorname{rank}_{\mathcal O} M[\wp]$ with the $\mathcal O$-length of $\mathcal O/\eta$; second, $M[\wp] = I \cdot M$, the image of the action of the ideal $I$ on the whole of $M$.
--
--   This is the equality case of the congruence-module inequality for a module $M$ over an augmented algebra $T$, in the form used in the module-theoretic numerical criterion of the Taylor–Wiles method; no reducedness of $T$ is assumed, the multiplicity-one input being $\eta \neq 0$. It is used in the criterion [`AlgHom.bijective_and_torsionBySet_eq_smul_of_length_le`](thm.html#AlgHom.bijective_and_torsionBySet_eq_smul_of_length_le) and in [`AlgHom.length_cotangent_mul_eq_length_quotient_of_free`](thm.html#AlgHom.length_cotangent_mul_eq_length_quotient_of_free).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_length_quotient_torsionBySet_sup_eq_iff.lean

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w x

theorem Module.length_quotient_torsionBySet_sup_eq_iff
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M] :
    Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) =
      (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) ↔
    Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤ := by sorry
