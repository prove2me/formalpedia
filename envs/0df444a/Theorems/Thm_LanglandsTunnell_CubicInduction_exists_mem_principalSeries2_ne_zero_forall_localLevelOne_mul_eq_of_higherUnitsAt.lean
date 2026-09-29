-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_principalSeries2_ne_zero_forall_localLevelOne_mul_eq_of_higherUnitsAt
-- name    : LanglandsTunnell.CubicInduction.exists_mem_principalSeries2_ne_zero_forall_localLevelOne_mul_eq_of_higherUnitsAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/d1978fc9-a1cb-5dc2-84f6-c7c2aae396e1
-- title:
--   A K₁(N)-fixed vector in the principal series I(θ₀,θ₁)
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, let $\theta_0,\theta_1$ be group homomorphisms from the units of the completion $\mathbb{Q}_p$ at $p$ to $\mathbb{C}^\times$, and let $c_0,c_1$ be natural numbers such that, for each $i$, $\theta_i(u)=1$ for every unit $u$ lying in `higherUnitsAt` at level $c_i$, i.e. every $u$ with $|u|=1$ and, when $c_i\neq 0$, $|u-1|\le \exp(-c_i)$ in the value group. Let $N$ be a non-zero ideal of $\mathcal{O}_{\mathbb{Q}}$ and $b$ a natural number with $p^b\mid N$ and $p^{b+1}\nmid N$, and assume $c_0+c_1\le b$. Then there exists a function $f\colon \mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ belonging to `principalSeries2` for $\theta$, that is: $f$ is locally constant, $f(\begin{pmatrix}1&x\\0&1\end{pmatrix}g)=f(g)$ for all $x\in\mathbb{Q}_p$ and all $g$, and $f(\mathrm{diag}(a_0,a_1)\,g)=\theta_0(a_0)\theta_1(a_1)\,\sqrt{\|a_0\|/\|a_1\|}\;f(g)$ for all units $a_0,a_1$ and all $g$; moreover $f\neq 0$ and $f(gk)=f(g)$ for all $g\in \mathrm{GL}_2(\mathbb{Q}_p)$ and all $k$ in [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) for $p$ and $N$, the subgroup of those $k$ whose image under the local embedding into $\mathrm{GL}_2$ of the finite adeles, together with the image of $k^{-1}$, satisfies the level-one congruence condition `IsLevelOneMatrix` modulo $N$.
--
--   This is the sufficiency half of Casselman's determination of the conductor of a principal series: when $p^{c_0+c_1}$ divides the $p$-part of $N$, the normalised principal series $I(\theta_0,\theta_1)$ of $\mathrm{GL}_2(\mathbb{Q}_p)$ contains a non-zero vector fixed by the local level-one group at $N$. It feeds the construction of an admissible principal-series vector with prescribed Whittaker and central-character behaviour used in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mem_principalSeries2_ne_zero_forall_localLevelOne_mul_eq_of_higherUnitsAt.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
  AutomorphicForm
open scoped nonZeroDivisors NNReal ENNReal

theorem LanglandsTunnell.CubicInduction.exists_mem_principalSeries2_ne_zero_forall_localLevelOne_mul_eq_of_higherUnitsAt
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)
    (hcb : c 0 + c 1 ≤ b) :
    ∃ f ∈ principalSeries2 p θ, f ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g := by sorry
