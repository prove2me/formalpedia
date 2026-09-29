-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_continuous_realization
-- name    : LanglandsTunnell.exists_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_continuous_realization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/1565ad53-c60f-5486-bca6-a73bd198164f
-- title:
--   Minimal-weight Casimir eigenvector inside one cuspidal constituent
-- statement:
--   Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients (a nonzero level ideal together with families $a_v,b_v$ indexed by the finite places), and let $R$ be a smooth cusp realization at the production pins `productionPinsGeneral ℚ` of the rescaled system `Φ.toRawCentral` (same level and same $a_v$, with $b_v$ replaced by $(\#(\mathcal{O}/v))^{-1}b_v$), so $R$ is a nowhere-identically-zero smooth cuspidal automorphic function with central character `R.centralChar`, invariant under the level subgroup, and a Hecke and central eigenfunction outside a finite exceptional set; $R$ is assumed continuous. Then there are a finite set $S$ of finite places containing `R.exceptionalSet` and an assignment $w \mapsto \mathrm{archR}(w)$ of a real archimedean parameter to each real infinite place, such that: every principal parameter $(u_1,a_1,u_2,a_2)$ occurring satisfies $|\mathrm{Re}(u_1-u_2)|<1$; the archimedean component of `R.centralChar`, read through the identification of the central subgroup with all of $(\mathbb{A}_{\mathbb{Q}})^\times$, is $x \mapsto \|x\|^{\mathrm{mult}(w)(e+1)}(x/\|x\|)^{s}$ where $e$ and $s$ are the central exponent and central sign of $\mathrm{archR}(w)$; and there exist $\varphi : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ and weights $k(w) \in \mathbb{Z}$ with the following properties. First, $\varphi$ is a nonzero continuous smooth cuspidal automorphic function with central character `R.centralChar`, invariant under the level-`Φ.level` subgroup, with Hecke eigenvalue $a_v$ and central eigenvalue $(\#(\mathcal{O}/v))^{-1}b_v$ for $v \notin S$, and $\varphi$ is reproduced by right convolution against some factorizable test function (a product of a compactly supported smooth archimedean factor and a compactly supported locally constant finite factor). Second, at each real place $\varphi$ transforms under the connected row-isometry subgroup by the $k(w)$-th power of the standard weight-one character; in the principal case $k(w) \in \{0,1\}$ and $k(w) \equiv a_1+a_2 \pmod 2$, and in the discrete case with parameter $(u_0,n)$, $n \ge 1$, one has $k(w) = n+1$. Third, $\varphi$ is archimedean-smooth at each real place and an eigenfunction of the Casimir operator there with eigenvalue $1/4-((u_1-u_2)/2)^2$ in the principal case and $(1-n^2)/4$ in the discrete case; in the principal case with $a_1 = a_2$ one has $\varphi(g \cdot J) = (-1)^{a_1}\varphi(g)$ for all $g$, where $J$ is the archimedean element coming from `UpperHalfPlane.J`; and in the discrete case, as well as in the principal case with $u_1 = u_2$ and $a_1 \ne a_2$, the combination $H\varphi - i(E\varphi + F^-\varphi)$ of the archimedean directional derivatives vanishes. Fourth, there is a subspace $V$ of functions on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ which is a cuspidal constituent for `R.centralChar` (a nonzero subspace of the $K$-finite cusp space, stable under right translation by finite-adelic elements and by connected row isometries at the infinite places and under right convolution by factorizable archimedean-bi-finite test functions, and minimal nonzero among such subspaces) with $\varphi \in V$, and some $\rho \in V$ whose first Whittaker coefficient with respect to the standard additive character $\psi_{\mathbb{Q}}$ is not identically zero and satisfies local multiplicity one at every finite place $p$: each $\psi_p$-equivariant linear functional on the local space attached to $\rho$ at $p$ is a fixed scalar multiple of evaluation at the identity. Finally, there is an idele unit $a$ with trivial finite component such that the first Whittaker coefficient of $\varphi$ is nonzero at $\mathrm{diag}(a,1)$.
--
--   This is the archimedean-classification and vector-selection step for the converse theorem in the Langlands–Tunnell argument: a continuous cuspidal realization of a Hecke eigensystem over $\mathbb{Q}$ is replaced by a vector of minimal $\mathrm{SO}(2)$-type which is a Casimir eigenvector with principal- or discrete-series parameters, chosen inside a single irreducible cuspidal constituent with a multiplicity-one Whittaker vector and with nonvanishing Whittaker coefficient on the archimedean torus. It feeds the statement establishing the Eulerian factorization of the Whittaker coefficient, [`LanglandsTunnell.exists_realArchParam_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_continuous_realization`](thm.html#LanglandsTunnell.exists_realArchParam_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_continuous_realization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_continuous_realization.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_WhittakerModelMultiplicityOne
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell.Converse NumberField.TateGlobal
open LanglandsTunnell

theorem LanglandsTunnell.exists_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_continuous_realization
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (_hR : Continuous R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam),
      R.exceptionalSet ⊆ S ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ)) ∧
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k : InfinitePlace ℚ → ℤ),
        IsIsotypicCuspFormAt ℚ
            (productionPinsGeneral ℚ)
            R.centralChar Φ.level S Φ φ ∧
        φ ≠ 0 ∧
        (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
            (k w = 0 ∨ k w = 1) ∧ ((k w : ZMod 2) = a₁ + a₂)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (archR w hw).laplaceEigenvalue • φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
            ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn →
            archDerivAt hw ArchDir.H φ
                - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
            archDerivAt hw ArchDir.H φ
                - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0) ∧

        (∃ V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
          CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) R.centralChar V ∧ φ ∈ V ∧
          ∃ ρ ∈ V, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ ρ 1 ≠ 0 ∧
            ∀ p : HeightOneSpectrum (𝓞 ℚ),
              AutomorphicForm.WhittakerModel.HasMultiplicityOneAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ ρ p (NumberField.StandardAddChar.psiV p)) ∧

        (∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 (diagOne a) ≠ 0) := by sorry
