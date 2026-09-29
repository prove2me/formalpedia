-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible
-- name    : LanglandsTunnell.RankinSelberg.dualPartner_block_of_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/24131049-09d4-5c0d-8092-0092e656fa6c
-- title:
--   Twisted contragredient of a Whittaker vector is again Whittaker
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal O_{\mathbb Q}$, a homomorphism $\theta_0$ from the units of the completion $\mathbb Q_p$ to $\mathbb C^\times$, and a nonzero ideal $N$ of $\mathcal O_{\mathbb Q}$. Let $w_2^{\mathrm{base}} : GL_2(\mathbb Q_p) \to \mathbb C$ satisfy: $w_2^{\mathrm{base}}(n(x)g) = \psi_p(x)\,w_2^{\mathrm{base}}(g)$ for all $x$ and $g$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the local component at $p$ of the standard adelic additive character; right invariance under the subgroup of $GL_2(\mathbb Q_p)$ pulled back along the local embedding into $GL_2(\mathbb A_{\mathbb Q}^{\mathrm f})$ from the level-one subgroup of level $N$; admissibility, namely for every open subgroup $U$ there is a finite set $B$ of functions such that every $U$-right-invariant element of the span of the right translates of $w_2^{\mathrm{base}}$ lies in the span of $B$; and $w_2^{\mathrm{base}}(zg) = \theta_0(z)\,w_2^{\mathrm{base}}(g)$ for scalar matrices $z$. Let $w_{0,p}$ and $d$ be elements of $GL_2(\mathbb Q_p)$ with matrices $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $\begin{pmatrix}1&0\\0&-1\end{pmatrix}$, and let $w$ lie in the span of the right translates of $w_2^{\mathrm{base}}$. Put $w^\flat(g) = \lvert\det(dg)\rvert\, w\bigl(w_{0,p}\,{}^{\mathsf T}(dg)^{-1}\bigr)$, with $\lvert\cdot\rvert$ the Haar modulus. Then $w^\flat$ is locally constant; $w^\flat(n(x)g) = \psi_p(x)\,w^\flat(g)$; $w^\flat$ is right invariant under some open subgroup; the span of the right translates of $w^\flat$ is admissible in the same sense; there is a homomorphism $\theta$ on the units with $w^\flat(zg) = \theta(z)\,w^\flat(g)$ for scalars $z$; and $w(-g) = \theta_0(-1)\,w(g)$ for all $g$.
--
--   This is the passage from a local Whittaker model to the Whittaker model of the contragredient representation, realised concretely by the twist $g \mapsto \lvert\det(dg)\rvert\,w(w_0\,{}^{\mathsf T}(dg)^{-1})$, which supplies the second argument in the local Rankin–Selberg integrals. It is used in the construction of the local zeta integrals at $p$ and in the verification of their functional equation for principal series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.dualPartner_block_of_admissible
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) → w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : ((w₀p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (d : GL (Fin 2) (p.adicCompletion ℚ)) (hd : ((d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; 0, -1])
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) :

    IsLocallyConstant (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) ∧

    (∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) g) ∧

    (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) (g * k) = (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) g) ∧

    (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧

    (∃ θ : (p.adicCompletion ℚ)ˣ →* ℂˣ, ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) g) ∧

    (∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) * g) = ((θ₀ (-1) : ℂˣ) : ℂ) * w g) := by sorry
