-- Prove2me | Theorems.Thm_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
-- name    : ModularCurve.modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/22cb9a1d-02ed-59ec-9335-b25a1f1aa905
-- title:
--   Ogg's unit Δ(q)/Δ(qᵖ) at the two components
-- statement:
--   Fix a nonzero natural number $N$ and a prime $p$ with $p \nmid N$, and write $F = \mathbb{Q}\bigl(\mathrm{qExpand}_{\mathbb{Q}}^{d}(j) : d \mid Np,\ d \neq 0\bigr) \subseteq \mathbb{Q}((q))$ for `modularFunctionFieldFull (N * p)`, the subfield of the Laurent series field generated over $\mathbb{Q}$ by the $q$-expansions $j(q^d)$ for the nonzero divisors $d$ of $Np$. Let $u =$ `modularUnitSeries p` $= \Delta \cdot \Delta(q^{p})^{-1}$, where $\Delta$ is the Laurent series $q\,\eta$-product used in the project and $\Delta(q^p)$ its $q \mapsto q^p$ substitution, and assume $u \in F$. Let $W_0, W_1$ be valuation subrings of $F$ subject to: $f \in W_0$ if and only if there are Laurent series $x, y$ with integer coefficients such that the coefficientwise reduction of $y$ modulo $p$ is nonzero and $f \cdot y = x$ in $\mathbb{Q}((q))$; and $f \in W_1$ if and only if $\sigma(f) \in W_0$, where $\sigma$ is `atkinLehnerInvolutionFull N p`, the chosen $\mathbb{Q}$-automorphism of $F$ interchanging $j(q^{d})$ and $j(q^{dp})$ for every nonzero $d \mid N$ (the identity if no such automorphism exists). The conclusion is fourfold: $u$ is the image of an integral Laurent series whose reduction modulo $p$ is nonzero; likewise $u^{-1}$; both $u$ and its inverse in $F$ lie in $W_0$; and both $u \cdot (p^{12})^{-1}$ and its inverse lie in $W_1$.
--
--   Ogg's modular unit $u = \Delta(q)/\Delta(q^{p})$ on $X_0(Np)$, with $W_0$ and $W_1$ playing the role of the local rings at the generic points of the two irreducible components of the special fibre of the integral model over $\mathbb{Z}_{(p)}$: the last two assertions express that $u$ has order $0$ along the component of $\infty$ and order $12$ along the component of $0$. It is used in the construction of the Deligne–Rapoport type model package at level $Np$, in particular in the étale- and chart-theoretic lemmas of [`ModularCurve.DRModelPackageLevel`](def/ModularCurve_DRModelPackageLevel.html#L71).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehnerPartial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (hmem : ModularCurve.modularUnitSeries p ∈ ModularCurve.modularFunctionFieldFull (N * p))
    (W₀ W₁ : ValuationSubring ↥(ModularCurve.modularFunctionFieldFull (N * p)))

    (hW₀ : ∀ f : ↥(ModularCurve.modularFunctionFieldFull (N * p)), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * ModularCurve.coeffMap (Int.castRingHom ℚ) y
          = ModularCurve.coeffMap (Int.castRingHom ℚ) x)

    (hW₁ : ∀ f : ↥(ModularCurve.modularFunctionFieldFull (N * p)), f ∈ W₁ ↔
      ModularCurve.atkinLehnerInvolutionFull N p f ∈ W₀) :

    (∃ x : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom (ZMod p)) x ≠ 0 ∧
        ModularCurve.modularUnitSeries p = ModularCurve.coeffMap (Int.castRingHom ℚ) x) ∧
    (∃ x : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom (ZMod p)) x ≠ 0 ∧
        (ModularCurve.modularUnitSeries p)⁻¹ = ModularCurve.coeffMap (Int.castRingHom ℚ) x) ∧

    ((⟨ModularCurve.modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull (N * p))) ∈ W₀ ∧
      (⟨ModularCurve.modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull (N * p)))⁻¹ ∈ W₀) ∧

    ((⟨ModularCurve.modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull (N * p))) *
          (((p : ℕ) : ↥(ModularCurve.modularFunctionFieldFull (N * p))) ^ 12)⁻¹ ∈ W₁ ∧
      ((⟨ModularCurve.modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull (N * p))) *
          (((p : ℕ) : ↥(ModularCurve.modularFunctionFieldFull (N * p))) ^ 12)⁻¹)⁻¹ ∈ W₁) := by sorry
