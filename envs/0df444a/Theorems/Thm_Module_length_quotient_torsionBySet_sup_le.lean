-- Prove2me | Theorems.Thm_Module_length_quotient_torsionBySet_sup_le
-- name    : Module.length_quotient_torsionBySet_sup_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/e9b86423-447a-558b-992d-05c9b4cfdb54
-- title:
--   Length bound for M/(M[wp]+M[I]) via the congruence ideal
-- statement:
--   Let $\mathcal{O}$ be a commutative domain that is a principal ideal ring, let $T$ be a commutative $\mathcal{O}$-algebra which is free as an $\mathcal{O}$-module, and let $\pi_T : T \to \mathcal{O}$ be an $\mathcal{O}$-algebra homomorphism. Write $\wp = \ker \pi_T$ and let $I = \operatorname{Ann}_T(\wp)$ be the annihilator ideal of $\wp$ in $T$; assume that the ideal $\eta = \pi_T(I)$ of $\mathcal{O}$, i.e. the image ideal `(RingHom.ker πT).annihilator.map πT`, is non-zero. Let $M$ be an abelian group carrying compatible $T$- and $\mathcal{O}$-module structures (the $\mathcal{O}$-action factoring through $T$ by a scalar tower) such that $M$ is finite and free as an $\mathcal{O}$-module. Let $M[\wp]$ and $M[I]$ denote the submodules of elements of $M$ annihilated by every element of $\wp$, respectively of $I$. Then the $\mathcal{O}$-module length of the quotient $M/(M[\wp] + M[I])$ is at most $\operatorname{rank}_{\mathcal{O}} M[\wp]$ times the $\mathcal{O}$-module length of $\mathcal{O}/\eta$, the inequality being one of elements of $\mathbb{N} \cup \{\infty\}$ with the rank coerced into $\mathbb{N}\cup\{\infty\}$. No freeness or reducedness conclusion about $T$ or $M$ is asserted.
--
--   This is the module-theoretic half of the congruence-module bookkeeping underlying the numerical criterion for complete intersections and multiplicity one, in Diamond's form: the non-vanishing of the congruence ideal $\eta = \pi_T(\operatorname{Ann}_T \ker \pi_T)$ controls how far $M$ is from being the sum of its $\wp$- and $I$-torsion. It is phrased purely in commutative algebra, and is used to derive [`AlgHom.bijective_and_torsionBySet_eq_smul_of_length_le`](thm.html#AlgHom.bijective_and_torsionBySet_eq_smul_of_length_le), where the reverse inequality forces the two torsion submodules to be in the expected position.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_length_quotient_torsionBySet_sup_le.lean

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

theorem Module.length_quotient_torsionBySet_sup_le
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M] :
    Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) ≤
      (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) := by sorry
