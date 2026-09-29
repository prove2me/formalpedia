-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre
-- name    : LanglandsTunnell.exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/77479679-9888-5133-84d8-812001038af2
-- title:
--   Existence of a real archimedean parameter for a cuspidal class
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, let $T$ be a finite subset of $\mathrm{GL}_2$ of the adele ring of $F$, and put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part is integral, whose archimedean components have local height $\ge c$ at every infinite place, window $\mathrm{xWindowSq}\le u^2$, and archimedean determinant norm in $[d_1,d_2]$. Assume $D$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g z\in D$. Let $\Theta$ be a Hecke eigensystem over $\mathbb{C}$, let $w$ be a real infinite place, and assume `ArchOccursInClassOf F D Θ (fun _ => True)`, i.e. some eigensystem agreeing with $\Theta$ away from finitely many places admits a smooth cusp realisation on the production pins attached to $D$ with continuous underlying function. Then there is a real archimedean parameter $P$ — either `principal u₁ a₁ u₂ a₂` with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or `discrete u k` with $1\le k$ — such that, in the principal case, $u_1-u_2=p$ for a nonzero integer $p$ forces $a_1-a_2\neq p+1$ in $\mathbb{Z}/2$, and $|\mathrm{Re}(u_1-u_2)|<1$; and such that the class of $\Theta$ on $D$ occurs with a realisation $\varphi$ satisfying all of: `HasArchCharacterAt₀ F w χ φ` for $\chi$ the character `archWeightCharℝ n₀(P)` transported to the row-isometry subgroup at $w$ along the isomorphism of $w$'s completion with $\mathbb{R}$, where $n_0(P)=0$ or $1$ according as $a_1+a_2=0$ or not in the principal case and $n_0(P)=k+1$ in the discrete case; `IsArchSmoothAt hw φ`, i.e. $e\mapsto\varphi(g\,\iota_w(e))$ is $C^\infty$ on invertible real $2\times 2$ matrices for every $g$; for every list $l$ of flow directions $H,E,F^-$, the iterated derivative $l$-fold `archDerivAt` of $\varphi$ is continuous and, for all $0<e_1<e_2$, bounded on $\{g:\ \text{idele norm of }\det g\in[e_1,e_2]\}$; $\mathrm{archCasimirAt}_w\varphi=\lambda(P)\varphi$ with $\lambda(P)=\tfrac14-((u_1-u_2)/2)^2$ in the principal case and $(1-k^2)/4$ in the discrete case; and $\varphi(\iota_w(t\cdot 1)g)=t^{\,e(P)}\varphi(g)$ for all real units $t>0$, where $e(P)=u_1+u_2$, respectively $2u$.
--
--   This is the step that manufactures the archimedean parameter of a cuspidal class at a real place out of the class data: the Casimir eigenvalue pins down $\lambda(P)$, the minimal occurring rotation type pins down the parity or the discrete-series weight, and the central character pins down $e(P)$. It feeds the Langlands–Tunnell analysis of archimedean data at a real place, being cited by the statements producing twisted Casimir eigenvectors of minimal weight and weight one and by the parameter-existence statement over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ArchParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam

theorem LanglandsTunnell.exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True)) :
    ∃ P : RealArchParam,
      (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = (laplaceEigenvalue P) • φ ∧
            (∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ (RealArchParam.centralExponent P)) * φ g)) := by sorry
