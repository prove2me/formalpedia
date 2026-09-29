-- Prove2me | Theorems.Thm_LanglandsTunnell_archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
-- name    : LanglandsTunnell.archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/2dae3289-8b1c-5dfe-bfa2-eb6426a77320
-- title:
--   Reflection J acts by (-1)^{a₁} on the weight-zero class
-- statement:
--   Fix reals $c,u,d_1,d_2$ with $0<c$, $0<d_1<d_2$, a finite set $T\subset \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and put $D=\bigcup_{x\in T}\{gx: g\in \mathfrak{S}\}$ where $\mathfrak{S}=$ `centreCutSiegelSet ℚ c u d₁ d₂` (finite part integral, all local heights $\ge c$, all window data $\le u^2$, all archimedean determinant norms in $[d_1,d_2]$), and assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ modulo left multiplication by $\mathrm{GL}_2(\mathbb{Q})$ and the adelic centre. Let $\Phi$ be a complex Hecke eigensystem over $\mathbb{Q}$ (a nonzero level ideal together with families $a_v,b_v$), $P$ a real archimedean parameter, $archC$ complex parameters at the complex places, and $d_R$, $d_C$ archimedean Whittaker data of those parameters. Hypothesis `hWF` asserts, in the sense of `ArchOccursInClassOf`, that some Hecke eigensystem agreeing with $\Phi$ away from a finite set of places admits a continuous cusp realization $\varphi$ on the production pins attached to $D$ (level subgroups $\mathrm{levelOne}\sqcap$ the finite-adelic subgroup, Hecke generators, box $\mathrm{adelicBox}$) for which there is $g_0$ with: the first Whittaker coefficient of $\varphi$ at the standard additive character is nonzero somewhere on the fibre $\{g:\ g_{\mathrm{fin}}=g_{0,\mathrm{fin}}\}$, and there is $z\in\mathbb{C}$ with that coefficient equal, on the whole fibre, to $\bigl(\prod_w \mathrm{archDetNorm}_w(g)^{\mathrm{mult}(w)}\bigr)^{-1/2}\,\mathrm{archW}(g)\,z$, where $\mathrm{archW}$ is the product over archimedean places of the data $d_R$ (all with parameter $P$) and $d_C$. Further hypotheses: at every real place $w$ the function $W=(d_R\,w)_{\!}.W$ satisfies $W(xr)=\mathrm{archWeightChar}_{\mathbb{R}}(n)(r)\,W(x)$ for $r$ in the row-isometry subgroup, with $n=0$ or $1$ according to whether $a_1+a_2=0$ in the principal case and $n=m+1$ in the discrete case; $W$ satisfies the Casimir equation $\mathrm{matrixCasimir}\,W=\lambda(P)W$ on invertible matrices, with $\lambda$ the Laplace eigenvalue of $P$; $W\not\equiv 0$; if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $a_1-a_2\ne p+1$ in $\mathbb{Z}/2$ for every nonzero integer $p$ with $u_1-u_2=p$, and $|\mathrm{Re}(u_1-u_2)|<1$; the central exponent of $P$ has vanishing real part; and finally $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$, the two sign exponents being equal. The conclusion is again of `ArchOccursInClassOf` shape for $D$ and $\Phi$: some eigensystem agreeing with $\Phi$ away from finitely many places has a continuous cusp realization $\varphi$ on those pins which satisfies `HasArchCharacterAt₀` at the real place of $\mathbb{Q}$ for $\mathrm{archWeightChar}_{\mathbb{R}}(0)$ transported along the identification of the completion with $\mathbb{R}$, is archimedean-smooth there, satisfies $\Omega_\infty\varphi=\lambda(P)\,\varphi$, and obeys $\varphi(g\cdot \mathrm{archRealGLAt}(J))=(-1)^{a_1.\mathrm{val}}\varphi(g)$ for all $g$, with $J=$ `UpperHalfPlane.J`.
--
--   This is the sign-pinning step in the archimedean half of the converse-theorem input to the Langlands–Tunnell argument: for a principal parameter with equal sign exponents the weight, the Casimir eigenvalue and the central character do not distinguish $P$ from its twist by $\mathrm{sgn}$, and the remaining invariant is the eigenvalue $\pm 1$ of the reflection $J$ on the weight-zero vector, here read off from the archimedean datum. It is used by the downstream statements producing, inside the near-equivalence class of $\Phi$, a twist with prescribed Casimir eigenvector, weight and nonvanishing Whittaker value.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen.lean

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
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

theorem LanglandsTunnell.archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
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
    (hP0 : (RealArchParam.centralExponent P).re = 0)
    (u₁ u₂ : ℂ) (a₁ : ZMod 2) (hP : P = RealArchParam.principal u₁ a₁ u₂ a₁) :
    ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
      (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧
        IsArchSmoothAt Rat.isReal_infinitePlace φ ∧
        archCasimirAt Rat.isReal_infinitePlace φ = (laplaceEigenvalue P) • φ ∧
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ g) := by sorry
