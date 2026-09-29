-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three
-- name    : LanglandsTunnell.CubicInduction.inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/d9995b08-507a-50c7-b167-8446ea15dbdb
-- title:
--   No cubic term at primes ramified in a cubic field
-- statement:
--   Let $K$ be a number field, equipped with an $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ which makes $\mathcal{O}_K$ integral over $\mathcal{O}_{\mathbb{Q}}$, and assume $[K:\mathbb{Q}] = \operatorname{finrank}_{\mathbb{Q}} K = 3$. Let $c$ be an arbitrary function from the height-one spectrum of $\mathcal{O}_K$ to $\mathbb{C}$ (no automorphy or multiplicativity is assumed of $c$), and let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ which is ramified in $K$ in the sense of `IsRamifiedIn`: there exists a height-one prime $\mathfrak{P}$ of $\mathcal{O}_K$ in the fibre of $v$, i.e. with $\mathfrak{P}$ contracting to $v$ along $\mathcal{O}_{\mathbb{Q}} \to \mathcal{O}_K$, whose ramification index $e(v,\mathfrak{P})$ is different from $1$. Then $\mathrm{inducedE3}\ \mathbb{Q}\ c\ v = 0$, that is, the coefficient of $X^3$ in the induced Euler polynomial $\mathrm{inducedEulerPoly}\ \mathbb{Q}\ c\ v$ — the finite product of the local factors $\mathrm{inducedFactor}\ \mathbb{Q}\ c\ \mathfrak{P}$ over the primes $\mathfrak{P}$ of $\mathcal{O}_K$ lying over $v$ — vanishes, since $\mathrm{inducedE3}$ is by definition the negative of that coefficient.
--
--   This is the degree bound on the Euler polynomial of an automorphic induction from a cubic field at a ramified place: ramification forces the total residue degree above $v$ to drop, so the induced Euler factor has degree at most $2$ and no cubic term. It is used in the construction of vectors of controlled level at places ramified in the cubic field, by [`LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound`](thm.html#LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_principalLevel_le_of_isRamifiedIn_of_isCubicInductionDataOn_of_conductorBound).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalWhittakerDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
  LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hram : IsRamifiedIn K v) :
    LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v = 0 := by sorry
