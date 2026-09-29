-- Prove2me | Theorems.Thm_NumberField_Idele_lintegral_mul_finprod_eq_lintegral_sPartMeasure_mul_iSup
-- name    : NumberField.Idele.lintegral_mul_finprod_eq_lintegral_sPartMeasure_mul_iSup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/75adbb42-83dc-540e-824b-a3d5a61880fb
-- title:
--   Factoring an idelic integral over the places outside S
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$, and let $S$ be a finite set of height-one primes of $\mathcal{O}_F$. Let $f$ be a function from the idele group $(\mathbb{A}_F)^\times$ to $[0,\infty]$, measurable for the Borel $\sigma$-algebra `ideleBorel F` on the unit group, and let $\varphi$ assign to each height-one prime $v$ a function $\varphi_v\colon\mathbb{Z}\to[0,\infty]$ such that $\varphi_v(0)=1$ whenever $v\notin S$. Write $\mathrm{ord}_v(a)=-\mathrm{WithZero.log}$ of the valuation of the $v$-component of the finite part of $a$, write $\mathrm{partAt}_S$ for the group endomorphism of $(\mathbb{A}_F)^\times$ induced by the monoid endomorphism of $\mathbb{A}_F$ that leaves the infinite component unchanged and applies `truncFin F S` to the finite component, and let `sPartMeasure F S` be the push-forward under $\mathrm{partAt}_S$ of the restriction of the Haar measure `idelicHaar F` to the subgroup of those unit ideles $\delta$ for which, for every $v\notin S$, the $v$-components of the finite parts of both $\delta$ and $\delta^{-1}$ lie in the $v$-adic valuation ring. Then the lower integral of $a\mapsto f(\mathrm{partAt}_S a)\cdot\prod_{v\notin S}\varphi_v(\mathrm{ord}_v a)$ against `idelicHaar F` equals the lower integral of $f$ against `sPartMeasure F S`, multiplied by the supremum, over finite sets $L$ of height-one primes disjoint from $S$, of $\prod_{v\in L}\sum_{m\in\mathbb{Z}}\varphi_v(m)$. The inner product over $v\notin S$ is taken as a `finprod`, and the sums over $\mathbb{Z}$ as `tsum` in $[0,\infty]$.
--
--   This is the Tonelli-type factorisation, in Tate's thesis style, of an integral over the idele group against Haar measure into its $S$-part and the local contributions of the places outside $S$, in the non-negative $[0,\infty]$-valued setting where no integrability hypothesis is needed. It is used in the global Tate theory of the project, namely in the construction of integrable majorants for norms of idelic integrands twisted by powers of the idele norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_lintegral_mul_finprod_eq_lintegral_sPartMeasure_mul_iSup.lean

import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.Idele MeasureTheory
open scoped ENNReal

theorem NumberField.Idele.lintegral_mul_finprod_eq_lintegral_sPartMeasure_mul_iSup
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hf : Measurable[ideleBorel F] f)
    (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) (hφ : ∀ v, v ∉ S → φ v 0 = 1) :
    (∫⁻ a, f (partAt F S a) * (∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ S), φ v (ord F v a))
        ∂(idelicHaar F)) =
      (∫⁻ a, f a ∂(sPartMeasure F S)) *
        ⨆ (L : Finset (HeightOneSpectrum (𝓞 F))) (_ : Disjoint L S), ∏ v ∈ L, ∑' m : ℤ, φ v m := by sorry
