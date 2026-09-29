-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries2_of_unramified
-- name    : LanglandsTunnell.CubicInduction.exists_spherical_mem_principalSeries2_of_unramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/d047e59e-2f64-5ca6-8f4a-a1ff47887d33
-- title:
--   Spherical vector in an unramified principal series of GL₂
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, so that $\mathbb{Q}_v$ denotes the corresponding completion, and let $\chi = (\chi_0,\chi_1)$ be a pair of group homomorphisms $\mathbb{Q}_v^{\times} \to \mathbb{C}^{\times}$. Assume each $\chi_i$ is unramified in the sense that $\chi_i(u) = 1$ whenever $u$ is a unit of $\mathbb{Q}_v$ with $\mathrm{Valued.v}(u) = 1$. The assertion is that there exists a function $f : \mathrm{GL}_2(\mathbb{Q}_v) \to \mathbb{C}$ belonging to the submodule `principalSeries2 v χ`, that is: $f$ is locally constant; $f(n(x)g) = f(g)$ for all $x \in \mathbb{Q}_v$ and $g$, where $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$; and $f(\mathrm{diag}(a_0,a_1)g) = \chi_0(a_0)\chi_1(a_1)\,\sqrt{\|a_0\|/\|a_1\|}\,f(g)$ for all units $a_0,a_1$ of $\mathbb{Q}_v$ and all $g$, the square root being the real one, cast to $\mathbb{C}$. Moreover $f$ is invariant under right translation by every $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the subgroup of $\mathrm{GL}_2(\mathbb{Q}_v)$ of elements whose image under the embedding `localEmbed` into $\mathrm{GL}_2$ of the finite adèles lies in `AdelicLevel.finiteLevelOne` for the unit ideal, i.e. such that the embedded matrix and its inverse both satisfy `IsLevelOneMatrix` at level $\top$; and $f(1) = 1$. Only existence is asserted, not uniqueness up to scalars.
--
--   This is the existence of the normalised spherical (level-one fixed) vector in the unramified principal series $I(\chi_0,\chi_1)$ of $\mathrm{GL}_2$ over a local field, normalised to take the value $1$ at the identity. It is used in the treatment of local Rankin–Selberg integrals for $\mathrm{GL}_3 \times \mathrm{GL}_2$, where it supplies the test vector whose Jacquet integral realises the unramified Whittaker function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries2_of_unramified.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.exists_spherical_mem_principalSeries2_of_unramified
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χ i u = 1) :
    ∃ f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ, f ∈ principalSeries2 v χ ∧
      (∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → f (g * k) = f g) ∧
      f 1 = 1 := by sorry
