-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_ker_comp_atkinLehner_le_comap_retraction_of_mem_ssJSet_of_not_dvd
-- name    : ModularCurve.IgusaScheme.ker_comp_atkinLehner_le_comap_retraction_of_mem_ssJSet_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/d329a8aa-b392-583b-9491-241a24599758
-- title:
--   Supersingular points of Y₀(N)_κ lie on the second copy
-- statement:
--   Let $N\ge 1$, let $p$ be a prime with $p \nmid N$, and write $\mathbf{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbf{Q}$ consisting of the rationals whose denominator is coprime to $p$. For $M\ge 1$, `modularFunctionFieldFull M` is the subfield of $\mathbf{Q}((q))$ generated over $\mathbf{Q}$ by the series $j(q^d)$ for the divisors $d$ of $M$, and `chartAlgFin M p` is its $\mathbf{Z}_{(p)}$-subalgebra of elements integral over $\mathbf{Z}_{(p)}[j]$. Let $\kappa$ be an algebraically closed field of characteristic $p$ which is a $\mathbf{Z}_{(p)}$-algebra. The data are: a $\mathbf{Z}_{(p)}$-algebra map $\iota$ from `chartAlgFin N p` to `chartAlgFin (N*p) p` preserving $q$-expansions; a $\mathbf{Z}_{(p)}$-algebra automorphism $w$ of `chartAlgFin (N*p) p` inducing `atkinLehnerInvolutionFull N p`; a $\kappa$-algebra map $\sigma_0 : \kappa\otimes_{\mathbf{Z}_{(p)}}$`chartAlgFin (N*p) p`$\to S:=\kappa\otimes_{\mathbf{Z}_{(p)}}$`chartAlgFin N p` retracting $\mathrm{id}_\kappa\otimes\iota$; and an element $v$ of `chartAlgFin (N*p) p` whose $q$-expansion is `modularUnitSeries p`$=\Delta(q)/\Delta(q^p)$. Assume $\kappa\otimes_{\mathbf{Z}_{(p)}}$`chartAlgFin (N*p) p` is reduced. Write $\sigma_1:=\sigma_0\circ(\mathrm{id}_\kappa\otimes w)$. Then: (A) for every prime ideal $\mathfrak{m}$ of $S$ containing $1\otimes j - a\otimes 1$ for some $a$ in `ssJSet p κ` (the $a\in\kappa$ such that every elliptic Weierstrass curve over $\kappa$ with $j$-invariant $a$ has no nonzero $p$-torsion point), one has $\ker\sigma_1\subseteq\sigma_0^{-1}(\mathfrak{m})$; and (B) for every maximal ideal $\mathfrak{m}$ of $S$ containing such an element, there is a maximal ideal $\mathfrak{m}_1$ of $S$ with $\sigma_1^{-1}(\mathfrak{m}_1)=\sigma_0^{-1}(\mathfrak{m})$.
--
--   This is the ring-theoretic form of the assertion that a supersingular point of the first copy of $Y_0(N)_\kappa$ inside $Y_0(Np)\otimes\kappa$ also lies on the second copy, hence is a crossing point of the two copies, as in the Deligne–Rapoport description of the reduction of $X_0(Np)$ at $p$. It is used in the identification of the nodes of the Igusa model with supersingular $j$-invariants, being cited by [`ModularCurve.IgusaScheme.forall_minimalPrimes_le_of_mem_ssJSet_tensor_chartAlgFin_mul_of_not_dvd`](thm.html#ModularCurve.IgusaScheme.forall_minimalPrimes_le_of_mem_ssJSet_tensor_chartAlgFin_mul_of_not_dvd) and by [`ModularCurve.DRLevel.exists_nodeEquiv_placeOfPoint_eq`](thm.html#ModularCurve.DRLevel.exists_nodeEquiv_placeOfPoint_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_ker_comp_atkinLehner_le_comap_retraction_of_mem_ssJSet_of_not_dvd.lean

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
open ModularCurve
open ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.ker_comp_atkinLehner_le_comap_retraction_of_mem_ssJSet_of_not_dvd
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
    [IsReduced (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))] :

    (∀ 𝔪 : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p)), 𝔪.IsPrime →
      (∃ a ∈ ssJSet p κ, (1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin N p -
          a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : ↥(chartAlgFin N p)) ∈ 𝔪) →
      RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom)) ≤ Ideal.comap σ₀ 𝔪) ∧

    (∀ 𝔪 : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p)), 𝔪.IsMaximal →
      (∃ a ∈ ssJSet p κ, (1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin N p -
          a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : ↥(chartAlgFin N p)) ∈ 𝔪) →
      ∃ 𝔪₁ : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p)), 𝔪₁.IsMaximal ∧
        Ideal.comap (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom)) 𝔪₁ = Ideal.comap σ₀ 𝔪) := by sorry
