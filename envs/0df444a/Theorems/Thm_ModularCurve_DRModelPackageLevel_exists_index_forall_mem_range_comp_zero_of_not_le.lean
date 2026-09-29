-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_index_forall_mem_range_comp_zero_of_not_le
-- name    : ModularCurve.DRModelPackageLevel.exists_index_forall_mem_range_comp_zero_of_not_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/5b087fc4-9472-51ae-a94a-955907d0d7ad
-- title:
--   Minimal primes over q in the Igusa chart select one component
-- statement:
--   Let $N_0\ge 1$ and let $q$ be a prime with $q\nmid N_0$, and let $\mathfrak P$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ q hqN` for the Igusa-type scheme $X =$ `X N₀ q` over $\operatorname{Spec}(R_q)$, $R_q =$ `DRLevel.R q`, whose structure morphism is `DRLevel.toBase N₀ q` $=$ `IgusaScheme.igusaTo (N₀ * q) q`. Write $A =$ `IgusaScheme.chartAlgFin (N₀ * q) q` for the finite-$j$ chart algebra, a subalgebra of the full modular function field of level $N_0q$, and $\iota =$ `IgusaScheme.ιFin (N₀ * q) q` for the associated chart morphism. Let $P\colon \mathrm{Fin}\,2\to$ ideals of $A$ be such that $P_0$ and $P_1$ are prime, distinct, and the set of minimal primes of the ideal $qA$ is exactly $\{P_0,P_1\}$. The assertion is that there exists an index $i\in\{0,1\}$ such that for every algebraically closed field $\kappa$ of characteristic $q$, every ring homomorphism $\mathrm{to}\kappa\colon R_q\to\kappa$, every point $y$ of the fibre `DRLevel.fibre toκ`, the pullback of `DRLevel.toBase N₀ q` along $\operatorname{Spec}(\mathrm{to}\kappa)$, and every prime $\mathfrak q\in\operatorname{Spec}A$: if the image of $y$ in $X$ under `pullback.fst` coincides with $\iota(\mathfrak q)$, and if $P_j\not\subseteq\mathfrak q$ for the index $j\ne i$, then $y$ lies in the image of the underlying continuous map of the morphism $\mathfrak P.\mathrm{comp}\,\kappa\,\mathrm{to}\kappa\,0$ and not in the image of that of $\mathfrak P.\mathrm{comp}\,\kappa\,\mathrm{to}\kappa\,1$. Note that the index $i$ is chosen once and for all, uniformly in $(\kappa,\mathrm{to}\kappa)$, while the two components named in the conclusion are fixed.
--
--   This is the topological dictionary between the two minimal primes of $q$ in the finite-$j$ chart ring of $X_0(N_0q)$ over $\mathbb Z_{(q)}$ and the two copies of $X_0(N_0)$ in the geometric fibre at $q$ supplied by the model package: the chosen index $i$ records which minimal prime lies under the first copy, in an orientation-free form. It feeds the chart-level statement [`ModularCurve.DRModelPackageLevel.exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one`](thm.html#ModularCurve.DRModelPackageLevel.exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one), used in the analysis of the bad fibre of $X_0(N_0q)$ at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_index_forall_mem_range_comp_zero_of_not_le.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve.DRModelPackageLevel

theorem exists_index_forall_mem_range_comp_zero_of_not_le
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (P : Fin 2 → Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (hP : ∀ i, (P i).IsPrime)
    (hmin : (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}).minimalPrimes = {P 0, P 1}) (hne : P 0 ≠ P 1) :
    ∃ i : Fin 2, ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
      (y : ↥(DRLevel.fibre (N₀ := N₀) toκ)) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)),
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 →
      (∀ j : Fin 2, j ≠ i → ¬ P j ≤ 𝔮.asIdeal) →
      y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∉ Set.range (𝔓.comp κ toκ 1).base := by sorry
