-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
-- name    : NumberField.TateGlobal.ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/2eac2fbd-836f-5417-9304-80ed7fabe62f
-- title:
--   Product formula for a principal idele split along S and T
-- statement:
--   Let $K$ be a number field (with decidable equality on the height one spectrum of $\mathcal O_K$), let $S$ and $T$ be finite sets of maximal ideals of $\mathcal O_K$ with $T$ disjoint from $S$, and let $a \in K^\times$. Write $a'$ for the image of $a$ in the units of the adele ring $\mathbb A_K$ under the algebra map $K \to \mathbb A_K$, and let [`NumberField.Idele.partAt`](def/NumberField_IdeleProductMeasure.html#L90) $K\,S$ be the group endomorphism of $\mathbb A_K^\times$ induced by the multiplicative map that leaves the infinite component unchanged and replaces the finite component by its truncation at $S$ (components at $v \in S$ unchanged, components at $v \notin S$ set to $1$). Here [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) $K$ of an idele is the real number underlying the value of the distributive Haar character `distribHaarChar` of $\mathbb A_K$ at that idele. The assertion is that the product of three quantities equals $1$: the idele norm of the $S$-part of $a'$; the finite product over $v \in T$ of $\|a\|_v$, the norm of the image of $a$ in the $v$-adic completion $K_v$; and the multiplicative finprod over all finite places $v$ of the factor which is $1$ when $v \in S \cup T$ and is $\|a\|_v$ otherwise.
--
--   This is the Artin–Whaples product formula for $a \in K^\times$, written in idelic form and regrouped according to the decomposition of the principal idele into its part at $S$ together with the infinite places and its components off $S$, with the places of $T$ separated out. It supplies the normalising identity used when translating global zeta integrals and orbital integrals by a principal idele, and is the source of the companion evaluation of the idele norm of the $S$-part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one.lean

import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.TateGlobal.ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S) (a : Kˣ) :
    NumberField.TateGlobal.ideleNorm K
        (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a)) *
      (∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (a : K)‖) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (if v ∈ S ∪ T then (1 : ℝ) else ‖algebraMap K (v.adicCompletion K) (a : K)‖) = 1 := by sorry
