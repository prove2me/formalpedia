-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_norm_apply_diagZ_mul_le_of_stabilised_jacquetIntegral_of_norm_eq_one
-- name    : LanglandsTunnell.CubicInduction.exists_norm_apply_diagZ_mul_le_of_stabilised_jacquetIntegral_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/c719dd9a-36b0-57e3-a8d6-53904600fbe1
-- title:
--   Moderate growth of the Jacquet integral along torus shells
-- statement:
--   Fix a height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ and a pair $\theta = (\theta_0,\theta_1)$ of group homomorphisms from the units of the completion $\mathbb{Q}_p$ to $\mathbb{C}^\times$, each unitary in the sense that $\|\theta_i(z)\| = 1$ for all units $z$, and suppose given $c : \mathrm{Fin}\,2 \to \mathbb{N}$ such that $\theta_i$ is trivial on `higherUnitsAt ℚ p (c i)`, the set of units $u$ with $v(u)=1$ and either $c_i = 0$ or $v(u-1) \le \exp(-c_i)$. Let $f : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ lie in `principalSeries2 p θ`, i.e. $f$ is locally constant, invariant under left translation by the upper unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $f(\mathrm{diag}(a_0,a_1)g) = \theta_0(a_0)\theta_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,f(g)$; assume further that $f$ is right invariant under some open subgroup $U$. Let $w_0$ be the element of $\mathrm{GL}_2(\mathbb{Q}_p)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, let $\psi$ be an additive character of $\mathbb{Q}_p$ trivial on some ball $\{v(y) \le \exp k\}$, and let $\varpi$ be an element of the valuation ring with nonzero image in $\mathbb{Q}_p$ of valuation $\exp(-1)$. Then, with the Borel $\sigma$-algebra on $\mathbb{Q}_p$, for every additive Haar measure $\nu$ and every function $W : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ with the property that for each $g$ there is $M_0 \in \mathbb{Z}$ such that for all $M \ge M_0$ the function $y \mapsto f(w_0\,\begin{pmatrix}1&y\\0&1\end{pmatrix}\,g)\psi(y)$ is integrable on $\{y : v(y) \le \exp M\}$ and $W(g)$ equals its integral there, there exist real constants $C$ and $A$ such that for all integers $m \ge 0$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the pullback along the local embedding into $\mathrm{GL}_2$ of the finite adeles of the level-one subgroup for the unit ideal) one has $\|W(\mathrm{diag}(\varpi^m,1)\,k)\| \le C\,(\mathrm{absNorm}\,p)^{A m}$.
--
--   This is the moderate-growth estimate for the stabilised Jacquet integral of a unitary principal-series vector of $\mathrm{GL}_2(\mathbb{Q}_p)$, bounding the associated Whittaker-type function on the torus shells $\mathrm{diag}(\varpi^m,1)K$ with $m \ge 0$ by $C\,q^{Am}$. It feeds the construction of a local Whittaker vector with prescribed central character and level for the principal series attached to $\theta$, used in the cubic-induction step of the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_norm_apply_diagZ_mul_le_of_stabilised_jacquetIntegral_of_norm_eq_one.lean

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

theorem LanglandsTunnell.CubicInduction.exists_norm_apply_diagZ_mul_le_of_stabilised_jacquetIntegral_of_norm_eq_one
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hθu : ∀ (i : Fin 2) (z : (p.adicCompletion ℚ)ˣ), ‖((θ i z : ℂˣ) : ℂ)‖ = 1)
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p θ)
    (hfsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (ψ : AddChar (p.adicCompletion ℚ) ℂ)
    (hψk : ∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → ψ y = 1)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure] (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ g : GL (Fin 2) (p.adicCompletion ℚ), ∃ M₀ : ℤ, ∀ M : ℤ, M₀ ≤ M →
          IntegrableOn (fun y : p.adicCompletion ℚ => f (w₀ * unipotentGL2 y * g) * ψ y)
            {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M} ν ∧
          W g = ∫ y in {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M},
            f (w₀ * unipotentGL2 y * g) * ψ y ∂ν) →
      ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ‖W (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
          C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m) := by sorry
