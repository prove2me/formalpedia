-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_measure_setOf_mem_localLevelOne_top_pos_and_lt_top
-- name    : LanglandsTunnell.RankinSelberg.measure_setOf_mem_localLevelOne_top_pos_and_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/25531dee-fb89-506d-8800-c02f4a312caa
-- title:
--   Haar measure of the unipotent part of the level-one group
-- statement:
--   Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$, and equip $\mathrm{GL}_2$ of the completion $\mathbb{Q}_v =$ `v.adicCompletion ℚ` with the Borel $\sigma$-algebra of its topology (`localGLBorel`). Consider the subgroup $N \le \mathrm{GL}_2(\mathbb{Q}_v)$ given as the range of the homomorphism `unipotentGL2Hom`, which sends $x$ in $\mathrm{Multiplicative}(\mathbb{Q}_v)$ to the unit with underlying matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and inverse $\begin{pmatrix}1&-x\\0&1\end{pmatrix}$, viewed as a type with its induced measurable structure. The assertion is: for every measure $\mu_N$ on $N$ that is a Haar measure, the subset of $N$ consisting of those $x$ whose image in $\mathrm{GL}_2(\mathbb{Q}_v)$ lies in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) — that is, the preimage under `localEmbed` (which inserts a matrix at the place $v$ and the identity elsewhere in $\mathrm{GL}_2$ of the finite adele ring) of the subgroup `AdelicLevel.finiteLevelOne` attached to the unit ideal $\top$, whose members are the $g$ with both $g$ and $g^{-1}$ satisfying the predicate `IsLevelOneMatrix` for $\top$ — has measure strictly between $0$ and $\infty$.
--
--   This is the elementary normalisation statement that the unipotent radical's intersection with the local level-one maximal compact subgroup has finite positive Haar volume; the quantity is the volume by which local Rankin–Selberg integrals over $N$ are normalised. It is used in the evaluation of the local Rankin–Selberg integral of the Jacquet–Whittaker function in the chamber computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_measure_setOf_mem_localLevelOne_top_pos_and_lt_top.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem
    LanglandsTunnell.RankinSelberg.measure_setOf_mem_localLevelOne_top_pos_and_lt_top
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ v
    ∀ (μN : Measure ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range)) [μN.IsHaarMeasure],
      0 < μN {x | (x : GL (Fin 2) (v.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤} ∧
        μN {x | (x : GL (Fin 2) (v.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤} < ⊤ := by sorry
