-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot
-- name    : LanglandsTunnell.exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/45b152d6-486e-54d7-b61c-5e90bb9570b0
-- title:
--   Whittaker fibre of a weight-one cusp form is a multiple of W_∞
-- statement:
--   Fix $u_1,u_2\in\mathbb{C}$ and $a_1,a_2\in\mathbb{Z}/2$ with $a_1\neq a_2$, $u_1\neq u_2$, subject to the genericity condition that for no nonzero integer $p$ with $u_1-u_2=p$ does $a_1-a_2$ equal $p+1$ in $\mathbb{Z}/2$, and to $|\mathrm{Re}(u_1-u_2)|<1$; write $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$. Let `archC` assign a complex archimedean parameter to each complex place of $\mathbb{Q}$, let `dR` assign to each real place an `ArchDatumR` for $P$ and `dC` the matching complex data. Assume each real datum's function $W$ transforms by the weight-one character `archWeightCharℝ 1` under right translation by `rowIsometrySubgroup₀ ℝ`, is a Casimir eigenfunction in the sense of `ArchCasimir.IsCasimirEigen` (matrix Casimir acting by $P$'s Laplace eigenvalue $1/4-((u_1-u_2)/2)^2$ on invertible matrices), and is not identically zero. Let $\kappa\in\mathbb{C}$ satisfy $\kappa^2(u_1-u_2)^2=1$ and, for every real place and every $x$ with $\det x\neq0$, $W(x\cdot\mathrm{diag}(-1,1))=\kappa\bigl(\partial_H W-\mathrm{i}(\partial_E W+\partial_{F^-}W)\bigr)(x)$, the derivatives being `ArchCasimir.matrixFlowDeriv` along the split torus and the two unipotent flows. Let $\xi$ be a character of the central subgroup of `productionPinsGeneral ℚ`, whose archimedean component at each real place is, in the sense of `IsArchCompAt`, the quasicharacter with exponent $P.\mathrm{centralExponent}+1$ and sign exponent $P.\mathrm{centralSign}$. Let $N\neq0$ be an ideal of $\mathbb{Z}$, $S$ a finite set of height-one primes, $\Phi$ a Hecke eigensystem over $\mathbb{C}$, and $\varphi:\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ an `IsIsotypicCuspFormAt` form for these data: a smooth cuspidal automorphic function with central character $\xi$, continuous, right invariant under the level subgroup $U(N)$, a Hecke eigenfunction with eigenvalue $\Phi.a\,v$ at each $v\notin S$, and with central eigenvalue $\Phi.\mathrm{toRawCentral}.b\,v$ there. Assume $\varphi$ lies in a submodule $V$ that is a cuspidal constituent (a cusp subrepresentation in the sense of `IsCuspSubrep`, nonzero, and minimal among such), that at each real place $\varphi$ has archimedean weight-one character, is `IsArchSmoothAt` with $\mathrm{archCasimirAt}\,\varphi$ equal to $P$'s Laplace eigenvalue times $\varphi$, that the three first flow-derivatives of $\varphi$ are continuous, and that $\varphi(g\cdot J)=\kappa\bigl(\partial_H\varphi-\mathrm{i}(\partial_E\varphi+\partial_{F^-}\varphi)\bigr)(g)$ for all $g$, where $J$ is inserted at the real place. Then for every $g_0$ with trivial archimedean component there is $z\in\mathbb{C}$ such that for every $g$ with the same finite part as $g_0$, the $\psi_\mathbb{Q}$-Whittaker coefficient of $\varphi$ at $\alpha=1$ evaluated at $g$ equals $\mathrm{archW}(P;\mathrm{archC},d_R,d_C)(g)\cdot z$.
--
--   This is the archimedean rigidity step in the converse-theorem input to Langlands–Tunnell: on each fibre of the finite-part map, the Whittaker coefficient of a weight-one cuspidal vector with prescribed Casimir eigenvalue and central behaviour is proportional to the assembled archimedean Whittaker function of the chosen datum, with the constant depending only on the fibre. It feeds the construction of a global form agreeing with the datum away from a finite set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

theorem LanglandsTunnell.exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂)
    (hgen : ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (htype : |(u₁ - u₂).re| < 1)
    (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hDW : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dR w hw))
    (hnv : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0)
    (κ : ℂ) (hκ : κ ^ 2 * (u₁ - u₂) ^ 2 = 1)
    (hDJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 →
      (dR w hw).W (x * Matrix.diagonal ![(-1 : ℝ), 1]) =
        κ * (ArchCasimir.matrixFlowDeriv ArchDir.H (dR w hw).W x -
              Complex.I * (ArchCasimir.matrixFlowDeriv ArchDir.E (dR w hw).W x +
                ArchCasimir.matrixFlowDeriv ArchDir.Fm (dR w hw).W x)))
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1)
        ((RealArchParam.principal u₁ a₁ u₂ a₂).centralSign.val : ℤ))
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V) (hφV : φ ∈ V)
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 1) φ)
    (hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue • φ)
    (hcont : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (d : ArchDir), Continuous (archDerivAt hw d φ))
    (hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (g * archRealGLAt hw UpperHalfPlane.J)
        = κ * (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) g) :
    ∀ g₀ : AdelicGL2 (𝓞 ℚ) ℚ, g₀ ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g
          = archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₂) archC dR dC g * z := by sorry
