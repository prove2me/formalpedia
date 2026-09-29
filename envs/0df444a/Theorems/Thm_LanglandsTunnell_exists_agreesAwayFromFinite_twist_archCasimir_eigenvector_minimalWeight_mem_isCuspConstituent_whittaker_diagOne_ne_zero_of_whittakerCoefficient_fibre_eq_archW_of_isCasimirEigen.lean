-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
-- name    : LanglandsTunnell.exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/0e064eeb-ad72-5130-a732-c54bebf90c54
-- title:
--   Selection of a minimal-weight cuspidal constituent with nonvanishing Whittaker vector
-- statement:
--   Fix reals $c,u,d_1,d_2$ with $0<c$, $0<d_1<d_2$, and a finite set $T\subset\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and put $D:=\bigcup_{x\in T} \{g x : g\in \mathrm{centreCutSiegelSet}\ \mathbb{Q}\ c\ u\ d_1\ d_2\}$, assumed (`hcov`) to satisfy `CoversModCentre`: every adelic $g$ can be written, after left multiplication by a rational point and right multiplication by a central idelic scalar, as an element of $D$. Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients, $P$ a real archimedean parameter, $archC$ a complex parameter at each complex place, and $dR$, $dC$ archimedean Whittaker data `ArchDatumR P`, `ArchDatumC (archC w hw)` at the real, respectively complex, places. The hypothesis `hWF` asserts `ArchOccursInClassOf` for $D$, $\Phi$ and the stated property: there are an eigensystem agreeing with $\Phi$ outside a finite set of primes and a genuine smooth cusp realization $\varphi$ of its raw central rescaling at the pins $\mathrm{productionPinsOf}\ \mathbb{Q}\ D$ (level subgroups $\mathrm{levelOne}\ N\sqcap$ the finite part, Hecke generators $\mathrm{heckeGen}$, conditioning box $\mathrm{adelicBox}$), together with $g_0$ such that the $\alpha=1$ Whittaker coefficient of $\varphi$ for the standard additive character is nonzero at some $g$ with $g_{\mathrm{fin}}=g_{0,\mathrm{fin}}$, and such that for some $z\in\mathbb{C}$ it equals $\bigl(\prod_{w\mid\infty}\mathrm{archDetNorm}_w(g)^{m_w}\bigr)^{-1/2}\,\mathrm{archW}(P,archC,dR,dC)(g)\cdot z$ on the whole fibre $g_{\mathrm{fin}}=g_{0,\mathrm{fin}}$. Further hypotheses on the real data: `hWT`, the Whittaker function $(dR\,w\,hw).W$ transforms under the row-isometry subgroup by the weight character $\mathrm{archWeightChar}_{\mathbb{R}}$ of weight $0$ or $1$ according to whether $a_1+a_2=0$ when $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$, and of weight $m+1$ when $P=\mathrm{discrete}(u,m)$; `hDE`, the Casimir eigen-law $\mathrm{matrixCasimir}\,W\,x=P.\mathrm{laplaceEigenvalue}\cdot W x$ for invertible $x$; `hnv`, $W\neq 0$; `hgen`, for principal $P$ and every nonzero integer $p$ with $u_1-u_2=p$ one has $a_1-a_2\neq p+1$ in $\mathbb{Z}/2$; `htype`, $|\mathrm{Re}(u_1-u_2)|<1$ for principal $P$; and `hP0`, $\mathrm{Re}(P.\mathrm{centralExponent})=0$. The conclusion produces a Hecke eigensystem $\Phi'$ agreeing with $\Phi$ away from finitely many primes, a finite set $S$ of primes, and a smooth cusp realization $R$ at $\mathrm{productionPinsGeneral}\ \mathbb{Q}$ of the raw central rescaling of the twist $\Phi'\otimes N^{-1/2}$ (so $a_v\mapsto \mathrm{N}(v)^{-1/2}a_v$, $b_v\mapsto \mathrm{N}(v)^{-1}b_v$ before the raw rescaling), such that $R$ is continuous, $R.\mathrm{exceptionalSet}\subseteq S$, and at each real place the central character of $R$, transported along the identification of the full unit group with the top subgroup, is the archimedean quasicharacter with exponent $P.\mathrm{centralExponent}+1$ and integer parameter $(P.\mathrm{centralSign}).\mathrm{val}$ in the sense of `IsArchCompAt`. Moreover there are a function $\varphi_1$, integer weights $k_1$ indexed by the infinite places, and a $\mathbb{C}$-submodule $V$ of functions on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ such that: $\varphi_1$ is a nonzero isotypic cusp form at the general pins for the central character $R.\mathrm{centralChar}$, the level of the twist, exceptional set $S$ and the twisted eigensystem; $\varphi_1$ is fixed by right convolution with some factorizable test function; at each real place $\varphi_1$ has archimedean character $\mathrm{archWeightCharAt}\,hw\,(k_1 w)$; for principal $P$, $k_1w\in\{0,1\}$ and $k_1w\equiv a_1+a_2$ mod $2$, while for discrete $P=\mathrm{discrete}(u_0,n)$, $k_1w=n+1$; $\varphi_1$ is archimedean-smooth at each real place with $\mathrm{archCasimirAt}\,\varphi_1=P.\mathrm{laplaceEigenvalue}\cdot\varphi_1$; if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ then $\varphi_1(g\cdot J)=(-1)^{a_1.\mathrm{val}}\varphi_1(g)$ for the archimedean element $J$ at $w$; and the lowering relation $\mathrm{archDerivAt}\,H\,\varphi_1-i(\mathrm{archDerivAt}\,E\,\varphi_1+\mathrm{archDerivAt}\,F^-\varphi_1)=0$ holds both for discrete $P$ and for principal $P$ with equal exponents and distinct signs $a_1\neq a_2$. Finally $V$ is a cuspidal constituent (`IsCuspConstituent`) at the general pins for $R.\mathrm{centralChar}$ containing $\varphi_1$, every $\varphi\in V$ has, at each finite place $p$, a local Whittaker space $\mathrm{localSpaceAt}$ for $\psi_{\mathbb{Q}}$ which is generated by any one of its nonzero vectors under right translation, has finite-dimensional $U$-fixed subspace for every open subgroup $U$ (a finite spanning set being supplied uniformly), and consists of vectors each fixed by some open subgroup; and there is an idele $a$ with trivial finite part such that the $\alpha=1$ Whittaker coefficient of $\varphi_1$ for $\psi_{\mathbb{Q}}$ at $\mathrm{diagOne}\,a$ is nonzero.
--
--   This is the selection step of the Whittaker link in the Langlands–Tunnell input: starting from a cusp form on a Siegel-covered region whose Whittaker coefficient factorises along an archimedean datum of minimal weight satisfying the Casimir eigen-law, it produces, at the general production pins, a continuous realization of the unitarily normalised eigensystem together with a nonzero vector inside an irreducible cuspidal constituent whose local Whittaker models are smooth admissible and cyclic, and with a nonvanishing Whittaker value on the diagonal torus. Its conclusion is exactly the hypothesis package of the subsequent Whittaker-link statement [`LanglandsTunnell.exists_agreesAwayFromFinite_isArithGenuineCuspRealizable_twist_whittaker_link_localSpaceAt_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen`](thm.html#LanglandsTunnell.exists_agreesAwayFromFinite_isArithGenuineCuspRealizable_twist_whittaker_link_localSpaceAt_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen.lean

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

theorem LanglandsTunnell.exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hWF : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archC dR dC g * z))
    (hWT : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ)))
    (hDE : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dR w hw))
    (hnv : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0)
    (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)))
    (htype : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1))
    (hP0 : (RealArchParam.centralExponent P).re = 0) :
    ∃ (Φ' : HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ))),
      Φ'.AgreesAwayFromFinite Φ ∧
      ∃ R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).toRawCentral,
      Continuous R.toFun ∧
      R.exceptionalSet ⊆ S ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ)) ∧
      ∃ (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)),
        (IsIsotypicCuspFormAt ℚ
            (productionPinsGeneral ℚ)
            R.centralChar (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).level S (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) φ₁) ∧
        (φ₁ ≠ 0) ∧
        (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
          P = RealArchParam.principal u₁ a₁ u₂ a₂ →
            (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          P = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = P.laplaceEigenvalue • φ₁) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          P = RealArchParam.principal u₁ a₁ u₂ a₁ →
            ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ₁ g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          P = RealArchParam.discrete u₀ n hn →
            archDerivAt hw ArchDir.H φ₁
                - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
          P = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
            archDerivAt hw ArchDir.H φ₁
                - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0) ∧

        CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) R.centralChar V ∧ φ₁ ∈ V ∧
        (∀ φ ∈ V,
              (∀ p : HeightOneSpectrum (𝓞 ℚ),
                ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ p φ,
                  W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ p φ,
                    W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                      fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
                (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
                  ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                    ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                      NumberField.StandardAddChar.psiQ p φ,
                      (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                        W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
                (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ p φ,
                  ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                    ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)))) ∧
        (∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 (diagOne a) ≠ 0) := by sorry
