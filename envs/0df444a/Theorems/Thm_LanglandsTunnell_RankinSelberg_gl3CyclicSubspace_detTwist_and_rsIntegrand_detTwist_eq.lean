-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_gl3CyclicSubspace_detTwist_and_rsIntegrand_detTwist_eq
-- name    : LanglandsTunnell.RankinSelberg.gl3CyclicSubspace_detTwist_and_rsIntegrand_detTwist_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/ed1ee387-cd44-5003-8095-10972aadee01
-- title:
--   Determinant twists cancel in the local GL₃× GL₂ Rankin–Selberg data
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$, write $\mathbb Q_p$ for the $p$-adic completion, let $\mu\colon\mathbb Q_p^\times\to\mathbb C^\times$ be a group homomorphism, let $W\colon GL_3(\mathbb Q_p)\to\mathbb C$ and $w\colon GL_2(\mathbb Q_p)\to\mathbb C$ be arbitrary functions, and let $w_{0,p}\in GL_2(\mathbb Q_p)$ have underlying matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Four assertions are made. First, for every $W_3\colon GL_3(\mathbb Q_p)\to\mathbb C$, the function $W_3$ lies in `gl3CyclicSubspace` of $(\mu\circ\det)\cdot W$ — the $\mathbb C$-span of the right translates $g\mapsto V(gh)$, $h\in GL_3(\mathbb Q_p)$ — if and only if $(\mu\circ\det)^{-1}W_3$ lies in `gl3CyclicSubspace` $W$. Second, for every $w_2\colon GL_2(\mathbb Q_p)\to\mathbb C$, $w_2$ lies in the $\mathbb C$-span of the functions $g\mapsto\mu(\det(gh))^{-1}w(gh)$, $h\in GL_2(\mathbb Q_p)$, if and only if $(\mu\circ\det)\cdot w_2$ lies in the span of the plain right translates $g\mapsto w(gh)$. Third, for all $W_3$, $w_2$ and all $s\in\mathbb C$, the functions on $GL_2(\mathbb Q_p)$ given by $\mu(\det\iota(g))W_3(\iota g)\cdot\mu(\det g)^{-1}w_2(g)\cdot\lVert\det g\rVert^{s-1/2}$ and by $W_3(\iota g)w_2(g)\lVert\det g\rVert^{s-1/2}$ are equal, where $\iota=$ `iotaGL` embeds $GL_2$ into $GL_3$ as the block $\mathrm{diag}(h,1)$ and $\lVert\cdot\rVert$ is `modulus`, the module of $\mathbb Q_p$ defined through `distribHaarChar`. Fourth, with $\widetilde V(x)=V(w_\ell\,{}^t x^{-1})$ for $w_\ell$ the $3\times3$ antidiagonal permutation matrix (`dualWhittakerFn3`), the functions $g\mapsto\widetilde{((\mu\circ\det)W_3)}(\iota g)\cdot\lVert\det g\rVert\,\mu(\det(w_{0,p}{}^tg^{-1}))^{-1}w_2(w_{0,p}{}^tg^{-1})\cdot\lVert\det g\rVert^{s-1/2}$ and $g\mapsto\widetilde{W_3}(\iota g)\cdot\lVert\det g\rVert\,w_2(w_{0,p}{}^tg^{-1})\cdot\lVert\det g\rVert^{s-1/2}$ coincide, for all $W_3$, $w_2$ and $s$.
--
--   This records that twisting a local $GL_3\times GL_2$ Rankin–Selberg pair by $\mu\circ\det$ on the $GL_3$ side and by $(\mu\circ\det)^{-1}$ on the $GL_2$ side leaves the cyclic space of right translates, the translate span and both the primal and the dual local integrands unchanged, the cancellations resting on $\det\iota(g)=\det g$ and $\det w_\ell=\det w_{0,p}=-1$. It is used in the construction of elements of the twisted $GL_3$ cyclic space with prescribed level and Whittaker behaviour at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_gl3CyclicSubspace_detTwist_and_rsIntegrand_detTwist_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.gl3CyclicSubspace_detTwist_and_rsIntegrand_detTwist_eq
    (p : HeightOneSpectrum (𝓞 ℚ)) (μ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (W : LocalGL3 p → ℂ) (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :

    (∀ W₃ : LocalGL3 p → ℂ,
      W₃ ∈ gl3CyclicSubspace (fun g : LocalGL3 p => ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W g) ↔
        (fun g : LocalGL3 p => ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W₃ g) ∈ gl3CyclicSubspace W) ∧
    (∀ w₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ,
      w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              ((μ (Matrix.GeneralLinearGroup.det (g * h)) : ℂˣ) : ℂ)⁻¹ * w (g * h)) ↔
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * w₂ g) ∈
          Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h))) ∧

    (∀ (W₃ : LocalGL3 p → ℂ) (w₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (s : ℂ),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((((μ (Matrix.GeneralLinearGroup.det (iotaGL g : LocalGL3 p)) : ℂˣ) : ℂ) * W₃ (iotaGL g)) * (((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w₂ g)) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) =
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))) ∧

    (∀ (W₃ : LocalGL3 p → ℂ) (w₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (s : ℂ),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (dualWhittakerFn3 (fun x : LocalGL3 p => ((μ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W₃ x) (iotaGL g) *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            (((μ (Matrix.GeneralLinearGroup.det (w₀p * transposeInvN (Fin 2) g)) : ℂˣ) : ℂ)⁻¹ * w₂ (w₀p * transposeInvN (Fin 2) g))) g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) =
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (dualWhittakerFn3 W₃ (iotaGL g) *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))) := by sorry
