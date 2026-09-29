-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd
-- name    : ModularCurve.IgusaScheme.exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/a018fa6f-2c6c-586f-b1b8-be8efc14ec8b
-- title:
--   Two minimal primes in the mod p chart of X₀(Np)
-- statement:
--   Let $N\ge 1$ and let $p$ be a prime with $p\nmid N$, and write $\mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. For $M\ge 1$ let $F_M$ be `modularFunctionFieldFull M`, the subfield of $\mathrm{LaurentSeries}\ \mathbb{Q}$ generated over $\mathbb{Q}$ by the expansions $j(q^d)$ for the nonzero divisors $d\mid M$, let $j_M\in F_M$ be the element `jFull M` given by $j(q)$, and let $\mathcal{O}_M=$ `chartAlgFin M p` be the $\mathbb{Z}_{(p)}$-subalgebra of elements of $F_M$ integral over $\mathbb{Z}_{(p)}[j_M]$, with distinguished element `jChartFin M p` $=j_M$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho:\mathbb{Z}_{(p)}\to A$ be a ring homomorphism compatible with the inclusions into $\overline{\mathbb{Q}}$; regard $\kappa$ as a $\mathbb{Z}_{(p)}$-algebra via $\rho$ followed by the residue map. Then there exist a $\mathbb{Z}_{(p)}$-algebra homomorphism $\iota:\mathcal{O}_N\to\mathcal{O}_{Np}$ which is the identity on underlying Laurent series, a $\mathbb{Z}_{(p)}$-algebra automorphism $w$ of $\mathcal{O}_{Np}$ whose effect on $F_{Np}$ is `atkinLehnerInvolutionFull N p` (the chosen $\mathbb{Q}$-algebra automorphism of $F_{Np}$ interchanging $j(q^d)$ and $j(q^{dp})$ for all nonzero $d\mid N$, the identity if none exists), and two $\kappa$-algebra homomorphisms $\sigma_0,\sigma_1:\kappa\otimes_{\mathbb{Z}_{(p)}}\mathcal{O}_{Np}\to\kappa\otimes_{\mathbb{Z}_{(p)}}\mathcal{O}_N$ such that: $\sigma_0\circ(\mathrm{id}_\kappa\otimes\iota)=\mathrm{id}$; $\sigma_1=\sigma_0\circ(\mathrm{id}_\kappa\otimes w)$ and $\sigma_1\circ(\mathrm{id}_\kappa\otimes(w\circ\iota))=\mathrm{id}$; the kernels of $\sigma_0$ and $\sigma_1$ are distinct minimal primes of $\kappa\otimes_{\mathbb{Z}_{(p)}}\mathcal{O}_{Np}$; $\sigma_0(1\otimes j_{Np})=1\otimes j_N$ while $\sigma_1(1\otimes j_{Np})=(1\otimes j_N)^p$; and every $u\in\mathcal{O}_{Np}$ whose image in $F_{Np}$ is $w(j_{Np})-j_{Np}^{\,p}$ satisfies $\sigma_0(1\otimes u)=0$ and $\sigma_1(1\otimes u)\neq 0$.
--
--   This is the chart-ring form, on the locus where $j$ is finite, of the Deligne–Rapoport description of the reduction of $X_0(Np)$ at a prime $p\nmid N$: the special fibre has two components, each a copy of the $j$-chart of $X_0(N)$ over $\kappa$, exchanged by $w_p$, on which $j$ restricts to $j$ and to $j^p$ respectively, and separated by the function $w_p(j)-j^p$. It is used downstream in the analysis of fibres of the Igusa-type model and of minimal primes over the chart algebras at level $\Gamma_0(Np)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open IsLocalRing ModularCurve ModularCurve.IgusaScheme

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) :
    letI := ((residue ↥A).comp ρ).toAlgebra
    ∃ (ι : ↥(chartAlgFin N p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
      (w : ↥(chartAlgFin (N * p) p) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)),

      (∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧
      (∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
        atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p)))) ∧
      ∃ σ : Fin 2 → (ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p) →ₐ[ResidueField ↥A]
          ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p)),

        (∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥A) (ResidueField ↥A)) ι z) = z) ∧

        (∀ z, σ 1 z = σ 0 (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥A) (ResidueField ↥A))
          (w : _ →ₐ[↥(GaloisRep.ratLocalizedAt p)] _) z)) ∧
        (∀ z, σ 1 (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥A) (ResidueField ↥A))
          ((w : _ →ₐ[↥(GaloisRep.ratLocalizedAt p)] _).comp ι) z) = z) ∧

        (∀ i, RingHom.ker (σ i) ∈
          minimalPrimes (ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))) ∧
        RingHom.ker (σ 0) ≠ RingHom.ker (σ 1) ∧

        σ 0 ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin (N * p) p) =
          (1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin N p ∧
        σ 1 ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin (N * p) p) =
          ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin N p) ^ p ∧

        ∀ u : ↥(chartAlgFin (N * p) p),
          (u : ↥(modularFunctionFieldFull (N * p))) =
            atkinLehnerInvolutionFull N p (jFull (N * p)) - jFull (N * p) ^ p →
          σ 0 ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] u) = 0 ∧
          σ 1 ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] u) ≠ 0 := by sorry
