-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm
-- name    : NumberField.TateGlobal.ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/4718a26d-e8a1-5c2b-9e54-85008d8ffc9c
-- title:
--   Idele norm of the S-part of a principal idele
-- statement:
--   Let $K$ be a number field and let $S$ be a finite set of finite places of $K$, i.e. a finite subset of the height-one spectrum of $\mathcal{O}_K$, and let $a \in K^{\times}$. Write $\iota(a)$ for the image of $a$ in $\mathbb{A}_K^{\times} = (\mathbb{A}_K)^{\times}$ under the unit map induced by the algebra map $K \to \mathbb{A}_K$, where the adele ring is realised as the product of its archimedean part $\prod_{w \mid \infty} K_w$ and the finite adele ring. The operator [`NumberField.Idele.partAt K S`](def/NumberField_IdeleProductMeasure.html#L90) is the unit-group homomorphism induced by the monoid endomorphism of $\mathbb{A}_K$ that leaves the archimedean component unchanged and replaces the finite component by its truncation `truncFin K S`, whose component at a finite place $v$ is the original one when $v \in S$ and $1$ otherwise. The assertion is that the idele norm of this truncated principal idele, namely the real number obtained from the value at it of the distributive Haar character `distribHaarChar` of $\mathbb{A}_K$, equals $$\Bigl(\prod_{w \mid \infty} \lVert \iota(a)_w \rVert^{\,m_w}\Bigr)\cdot \prod_{v \in S} \lVert \iota(a)_v \rVert,$$ the first product being over the infinite places $w$ of $K$ with $m_w$ the multiplicity `InfinitePlace.mult` of $w$, and the second over the finite places in $S$, with the norms taken in the respective completions.
--
--   This is the local–global splitting of the idele norm (module) for principal ideles truncated outside a finite set of finite places: only the archimedean places and the places of $S$ contribute, and they contribute their local absolute values. It is used in the analytic part of the project, where class sums and orbital integrals of automorphic forms are rewritten as lattice sums weighted by idele norms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm.lean

import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.TateGlobal.ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    NumberField.TateGlobal.ideleNorm K
        (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a)) =
      (∏ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) (a : K)).1 w‖ ^ w.mult) *
        ∏ v ∈ S, ‖((algebraMap K (AdeleRing (𝓞 K) K) (a : K)).2 : FiniteAdeleRing (𝓞 K) K) v‖ := by sorry
