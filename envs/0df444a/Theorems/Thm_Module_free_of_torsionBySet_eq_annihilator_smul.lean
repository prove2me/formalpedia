-- Prove2me | Theorems.Thm_Module_free_of_torsionBySet_eq_annihilator_smul
-- name    : Module.free_of_torsionBySet_eq_annihilator_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/e97da186-7103-5e4f-8e6e-f63e0a467df5
-- title:
--   Freeness over T from saturation, duality and rank equality
-- statement:
--   Let $\mathcal O$ be a principal ideal domain and let $T$ be a commutative local ring equipped with an $\mathcal O$-algebra structure making it module-finite and free over $\mathcal O$. Let $\pi_T : T \to \mathcal O$ be an $\mathcal O$-algebra homomorphism, write $\wp = \ker \pi_T$ for its kernel and $I = \operatorname{Ann}_T(\wp)$ for the annihilator ideal of $\wp$ in $T$, and assume that the image ideal $\pi_T(I) \subseteq \mathcal O$ is nonzero. Let $C : T \times T \to \mathcal O$ be an $\mathcal O$-bilinear form satisfying $C(st, u) = C(t, su)$ for all $s, t, u \in T$ and such that $t \mapsto C(t, -)$ is a bijection of $T$ onto $\operatorname{Hom}_{\mathcal O}(T, \mathcal O)$. Let $M$ be a $T$-module, also an $\mathcal O$-module compatibly with the $T$-action, module-finite and free over $\mathcal O$, and let $B : M \times M \to \mathcal O$ be an $\mathcal O$-bilinear form with $B(t \cdot m, n) = B(m, t \cdot n)$ for all $t \in T$, $m, n \in M$, such that $m \mapsto B(m,-)$ is a bijection of $M$ onto $\operatorname{Hom}_{\mathcal O}(M, \mathcal O)$. Assume further the rank equality $\operatorname{rank}_{\mathcal O} M = \operatorname{rank}_{\mathcal O} M[\wp] \cdot \operatorname{rank}_{\mathcal O} T$, where $M[\wp] = \{m \in M : \lambda m = 0 \text{ for all } \lambda \in \wp\}$, and the saturation identity $M[\wp] = I \cdot M$. Then $M$ is free as a $T$-module.
--
--   This is the freeness step in the module-theoretic form of the numerical criterion of the Taylor–Wiles method: a Gorenstein-type duality datum $C$ on $T$ together with a perfect $T$-invariant pairing $B$ on $M$, the generic-rank (multiplicity one) equality and the saturation $M[\wp] = I \cdot M$ force integral freeness over $T$, by the adjoint argument of Wiles's appendix transported to modules. It is used in [`AlgHom.bijective_and_free_of_length_le`](thm.html#AlgHom.bijective_and_free_of_length_le), where freeness over the Hecke-type algebra is combined with a length inequality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_free_of_torsionBySet_eq_annihilator_smul.lean

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

theorem Module.free_of_torsionBySet_eq_annihilator_smul
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u)) (hCb : Function.Bijective C)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (hrank : Module.finrank 𝒪 M =
      Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) * Module.finrank 𝒪 T)
    (hsat : Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤) :
    Module.Free T M := by sorry
