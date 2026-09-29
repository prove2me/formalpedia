-- Prove2me | Theorems.Thm_IsRegularLocalRing_exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem
-- name    : IsRegularLocalRing.exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/e746f5de-a501-5362-82d5-f82ae9602ed2
-- title:
--   Étale base change of tame cyclic cover data
-- statement:
--   Let $R$ be a regular local domain, complete with respect to its maximal ideal, with $\mathfrak m_R = (\varpi, s)$ for given $\varpi, s \in R$ and $\operatorname{ringKrullDim} R = 2$, and let $e$ be a positive natural number whose image in $R$ is a unit. Let $B$ be a Noetherian integrally closed local domain which is an $R$-algebra, module-finite over $R$ and with $R \to B$ injective (`FaithfulSMul`), let $K_0$ be a fraction field of $R$ and $F$ a fraction field of $B$, arranged so that $F$ is a $K_0$-algebra compatibly with the maps from $R$ and $B$, with $F/K_0$ finite Galois, $\operatorname{Gal}(F/K_0)$ cyclic and $[F:K_0] = e$. Assume further that $B$ is unramified over $R$ at every prime $\mathfrak p \subset B$ whose contraction to $R$ has height $1$ and does not contain $s$, and that the residue extension is trivial in the strong form: every $b \in B$ differs from the image of some $r \in R$ by an element of $\mathfrak m_B$. Finally let $R'$ be a regular local domain in the same universe as $R$, an $R$-algebra which is module-finite, free, faithful and étale over $R$, and complete for its maximal ideal. The conclusion asserts the existence of a type $B'$ carrying the structure of a Noetherian integrally closed local domain with an $R'$-algebra structure making it module-finite and faithful over $R'$, together with a fraction field $K_0'$ of $R'$ and a fraction field $F'$ of $B'$, with $F'$ a $K_0'$-algebra compatibly with $R'$ and $B'$, such that $F'/K_0'$ is finite Galois with cyclic Galois group and $[F':K_0'] = e$, such that $B'$ is unramified over $R'$ at every prime of $B'$ whose contraction to $R'$ has height $1$ and omits the image of $s$, such that every element of $B'$ is congruent modulo $\mathfrak m_{B'}$ to the image of an element of $R'$, and such that there is an $R'$-algebra isomorphism $R' \otimes_R B \cong B'$.
--
--   This is the base-change step for Abhyankar's lemma at a smooth point: the package of hypotheses on a tame cyclic cover $B/R$ of a two-dimensional complete regular local base, ramified only along $s$ in height one and with trivial residue extension, is transported along a finite étale local extension $R \to R'$, the new cover being $R' \otimes_R B$. It feeds the construction of an explicit Kummer presentation of such covers in [`IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue`](thm.html#IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue), and it uses that regularity, dimension two, the shape of the maximal ideal and completeness all persist under finite étale local base change, and that normality of $B$ persists after tensoring with an étale algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsRegularLocalRing_exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial
open scoped TensorProduct

universe u v w x

theorem IsRegularLocalRing.exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (ϖ s : R) (hmax : maximalIdeal R = Ideal.span {ϖ, s}) (hdim : ringKrullDim R = 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R))
    (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type w) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type x) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = e)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R B)).height = 1 →
      s ∉ 𝔭.comap (algebraMap R B) → Algebra.IsUnramifiedAt R 𝔭)
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (R' : Type u) [CommRing R'] [IsRegularLocalRing R'] [IsDomain R'] [Algebra R R']
    [Module.Finite R R'] [Module.Free R R'] [FaithfulSMul R R'] [Algebra.Etale R R']
    [IsAdicComplete (maximalIdeal R') R'] :
    ∃ (B' : Type (max u v)) (_ : CommRing B') (_ : IsDomain B') (_ : IsIntegrallyClosed B') (_ : IsLocalRing B')
      (_ : IsNoetherianRing B') (_ : Algebra R' B') (_ : Module.Finite R' B') (_ : FaithfulSMul R' B')
      (K₀' : Type u) (_ : Field K₀') (_ : Algebra R' K₀') (_ : IsFractionRing R' K₀')
      (F' : Type (max u v)) (_ : Field F') (_ : Algebra K₀' F') (_ : Algebra R' F') (_ : IsScalarTower R' K₀' F')
      (_ : Algebra B' F') (_ : IsScalarTower R' B' F') (_ : IsFractionRing B' F')
      (_ : FiniteDimensional K₀' F') (_ : IsGalois K₀' F'),
      IsCyclic (F' ≃ₐ[K₀'] F') ∧ Module.finrank K₀' F' = e ∧
      (∀ (𝔭 : Ideal B') [𝔭.IsPrime], (𝔭.comap (algebraMap R' B')).height = 1 →
        algebraMap R R' s ∉ 𝔭.comap (algebraMap R' B') → Algebra.IsUnramifiedAt R' 𝔭) ∧
      (∀ b : B', ∃ r : R', b - algebraMap R' B' r ∈ maximalIdeal B') ∧
      Nonempty (R' ⊗[R] B ≃ₐ[R'] B') := by sorry
