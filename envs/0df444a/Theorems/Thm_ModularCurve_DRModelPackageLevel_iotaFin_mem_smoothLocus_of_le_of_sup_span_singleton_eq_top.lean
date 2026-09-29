-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
-- name    : ModularCurve.DRModelPackageLevel.iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/b40de69f-5c77-5179-8014-7dc81938d6d5
-- title:
--   Finite-j chart level sets lie in the smooth locus
-- statement:
--   Fix a nonzero natural number $N_0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel N₀ q hqN`, that is, a bundle consisting of the scheme `X N₀ q` over $\operatorname{Spec} R_q$ together with its structural properties (properness, flatness, integrality, local finite presentation, normality on affine opens of `X N₀ q`), a curve model `Meta` for the modular function field of level $N_0q$ over $\overline{\mathbb Q}$ with an isomorphism `eeta` onto the $\overline{\mathbb Q}$-fibre compatible with the Galois action and with the $q$-expansion pinning `Meta_pin`, smoothness of relative dimension $1$ and geometric integrality of the fibre over $\mathbb Q$, sections `εinf`, `εzero` over the base, and the further data recorded in the structure, among them the distinguished subset `𝔓.smoothLocus` of `X N₀ q` and, for each ring homomorphism $\mathrm{to}\kappa : R_q \to \kappa$ and each index $i$, a morphism `𝔓.comp κ toκ i` into the fibre of `toBase N₀ q` along $\operatorname{Spec}(\mathrm{to}\kappa)$. Let $v$ be an element of the finite-$j$ chart algebra `IgusaScheme.chartAlgFin (N₀ * q) q`, the $R_q$-subalgebra `chartAlg (N₀*q) q {jFull (N₀*q)}` of the full modular function field of level $N_0q$, and write $A$ for that algebra and $\iota_{\mathrm{fin}} =$ `IgusaScheme.ιFin (N₀ * q) q` for the chart morphism $\operatorname{Spec} A \to$ `X N₀ q`. Assume the dictionary hypothesis `hdict`: for every algebraically closed field $\kappa$ of characteristic $q$, every homomorphism $\mathrm{to}\kappa : R_q \to \kappa$, every point $y$ of the fibre and every prime $\mathfrak q$ of $A$ such that the first projection of the fibre sends $y$ to $\iota_{\mathrm{fin}}(\mathfrak q)$ and $v \notin \mathfrak q$, the point $y$ lies in the range of `(𝔓.comp κ toκ 0).base` and not in the range of `(𝔓.comp κ toκ 1).base`. Let $I \subseteq A$ be an ideal such that $A/I$ is module-finite over $R_q$ and $I + (v) = A$. Then for every prime $\mathfrak q$ of $A$ containing $I$, the point $\iota_{\mathrm{fin}}(\mathfrak q)$ of `X N₀ q` belongs to `𝔓.smoothLocus`.
--
--   This supplies the geometric clause that the zero set in the finite-$j$ chart of an ideal with module-finite quotient over the base, coprime to the dictionary coordinate $v$, lies entirely inside the smooth locus of the Deligne–Rapoport model of level $N_0q$ over $R_q$. It is used in the construction of one-sided pools from level polynomials, via `exists_oneSidedPool_baseChange_of_levelPolynomials`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve.DRModelPackageLevel

theorem iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hdict : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
      (y : ↥(fibre (N₀ := N₀) toκ)) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)),
      (pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 →
      v ∉ 𝔮.asIdeal → y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∉ Set.range (𝔓.comp κ toκ 1).base)
    (I : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) [Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)]
    (hIv : I ⊔ Ideal.span {v} = ⊤)
    (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (h𝔮 : I ≤ 𝔮.asIdeal) :
    (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 ∈ (𝔓.smoothLocus : Set ↥(X N₀ q)) := by sorry
