-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finite_free_quotient_bialgHom
-- name    : HopfAlgebra.exists_finite_free_quotient_bialgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/a62367c3-4e76-5f6b-8e20-6b38cbef15b2
-- title:
--   Finite free Hopf quotient of a finite Hopf algebra over a PID
-- statement:
--   Let $R$ be a commutative ring which is a domain and a principal ideal ring, and let $A$ be a commutative ring carrying the structure of a Hopf algebra over $R$ which is finite as an $R$-module. The assertion is the existence of a type $B$ (in the same universe as $A$) together with a commutative ring structure, a Hopf algebra structure over $R$, and a bialgebra homomorphism $\pi \colon A \to B$ over $R$, such that: $B$ is finite as an $R$-module, free as an $R$-module, and flat as an $R$-module; if the comultiplication of $A$ is cocommutative then so is that of $B$; the underlying function of $\pi$ is surjective; and for every type $L$ (in an arbitrary universe) equipped with a commutative ring structure, an $R$-algebra structure, and which is torsion-free as an $R$-module, the map sending an $R$-algebra homomorphism $f \colon B \to L$ to the composite of the underlying $R$-algebra homomorphism of $\pi$ with $f$ is a bijection onto the $R$-algebra homomorphisms $A \to L$.
--
--   In geometric language: a finite group scheme over a principal ideal domain admits a closed subgroup scheme that is finite and free over the base and has the same points in every torsion-free $R$-algebra, the quotient being $A$ modulo its $R$-torsion. It is used to produce finite flat Hopf-algebra models of torsion of Weierstrass curves, in [`WeierstrassCurve.exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor`](thm.html#WeierstrassCurve.exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor) and [`WeierstrassProjModel.exists_finiteFree_hopfAlgebra_padicInt_rank_psq_of_isPointsEval_of_flat`](thm.html#WeierstrassProjModel.exists_finiteFree_hopfAlgebra_padicInt_rank_psq_of_isPointsEval_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finite_free_quotient_bialgHom.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.exists_finite_free_quotient_bialgHom
    (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing A] [HopfAlgebra R A] [Module.Finite R A] :
    ∃ (B : Type v) (_ : CommRing B) (_ : HopfAlgebra R B) (π : A →ₐc[R] B),
      Module.Finite R B ∧ Module.Free R B ∧ Module.Flat R B ∧
      (Coalgebra.IsCocomm R A → Coalgebra.IsCocomm R B) ∧
      Function.Surjective ⇑π ∧
      ∀ (L : Type w) [CommRing L] [Algebra R L] [Module.IsTorsionFree R L],
        Function.Bijective (fun f : B →ₐ[R] L => f.comp (π : A →ₐ[R] B)) := by sorry
