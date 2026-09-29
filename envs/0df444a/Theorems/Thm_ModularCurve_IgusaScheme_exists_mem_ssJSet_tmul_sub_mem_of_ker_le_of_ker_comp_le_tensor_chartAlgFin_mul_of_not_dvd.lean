-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_mem_ssJSet_tmul_sub_mem_of_ker_le_of_ker_comp_le_tensor_chartAlgFin_mul_of_not_dvd
-- name    : ModularCurve.IgusaScheme.exists_mem_ssJSet_tmul_sub_mem_of_ker_le_of_ker_comp_le_tensor_chartAlgFin_mul_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/129c7c26-66b3-5569-a1ed-0033df6c4432
-- title:
--   Crossing primes on X₀(Np) have supersingular j-invariant
-- statement:
--   Fix natural numbers $N$ (nonzero) and $p$ (prime) with $p \nmid N$, and let $\kappa$ be an algebraically closed field of characteristic $p$, equipped with decidable equality and with an algebra structure over the subring $\mathbb{Z}_{(p)} =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of rationals whose denominator is coprime to $p$. Write $A(M)$ for `chartAlgFin M p`, the $\mathbb{Z}_{(p)}$-subalgebra of the field `modularFunctionFieldFull M` consisting of the elements integral over $\mathbb{Z}_{(p)}[j]$. The data are: a $\mathbb{Z}_{(p)}$-algebra map $\iota : A(N) \to A(Np)$ which on Laurent $q$-expansions is the identity inclusion; a $\mathbb{Z}_{(p)}$-algebra automorphism $w$ of $A(Np)$ inducing `atkinLehnerInvolutionFull N p`, the chosen automorphism of `modularFunctionFieldFull (N*p)` interchanging the $q$-expansions of $j(d\tau)$ and $j(dp\tau)$ for every divisor $d \mid N$ (the identity if no such automorphism exists); a $\kappa$-algebra map $\sigma_0 : \kappa \otimes_{\mathbb{Z}_{(p)}} A(Np) \to \kappa \otimes_{\mathbb{Z}_{(p)}} A(N)$ which is a retraction of $\mathrm{id}_\kappa \otimes \iota$, i.e. $\sigma_0((\mathrm{id} \otimes \iota)(z)) = z$ for all $z$; an element $v \in A(Np)$ whose $q$-expansion is `modularUnitSeries p`, that is $\Delta(\tau)\,\Delta(p\tau)^{-1}$; and a prime ideal $\mathfrak{q}$ of $\kappa \otimes_{\mathbb{Z}_{(p)}} A(Np)$ containing both $\ker \sigma_0$ and $\ker(\sigma_0 \circ (\mathrm{id}_\kappa \otimes w))$. The conclusion is that there is an $a \in \kappa$ lying in `ssJSet p κ` — i.e. such that every elliptic Weierstrass curve over $\kappa$ with $j$-invariant $a$ has no nonzero $p$-torsion point — with $1 \otimes j - a \otimes 1 \in \mathfrak{q}$, where $j$ denotes `jChartFin (N*p) p`.
--
--   This is the implication "crossing point $\Rightarrow$ supersingular" for the fibre at $p$ of the modular curve of level $Np$: a prime of the fibre ring lying on both the level-$N$ chart and its Atkin–Lehner translate has supersingular $j$-invariant. It is used in the analysis of the Igusa-type fibre, being cited by the results on primes of `chartAlgFin` of level $\Gamma_0(N)\cdot p$ that place $j$ in `ssJSet p κ` when two minimal primes are present.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_mem_ssJSet_tmul_sub_mem_of_ker_le_of_ker_comp_le_tensor_chartAlgFin_mul_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct
open ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_mem_ssJSet_tmul_sub_mem_of_ker_le_of_ker_comp_le_tensor_chartAlgFin_mul_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

    (ι : ↥(chartAlgFin N p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
    (hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
      atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))))

    (σ₀ : κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p) →ₐ[κ]
        κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)

    (v : ↥(chartAlgFin (N * p) p))
    (hv : ((v : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) = modularUnitSeries p)

    (𝔮 : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))) [𝔮.IsPrime]
    (h𝔮₀ : RingHom.ker σ₀ ≤ 𝔮)
    (h𝔮₁ : RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) (w : ↥(chartAlgFin (N * p) p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)))) ≤ 𝔮) :
    ∃ a ∈ ssJSet p κ, (1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin (N * p) p -
        a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : ↥(chartAlgFin (N * p) p)) ∈ 𝔮 := by sorry
