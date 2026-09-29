-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isArithGenuineCuspRealizable_twist_of_coversModCentre_centreCut
-- name    : LanglandsTunnell.exists_isArithGenuineCuspRealizable_twist_of_coversModCentre_centreCut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/3d6db657-940a-5fea-8c4b-2deb96578316
-- title:
--   Twist-stability of arithmetic genuine cusp-realizability on a covering window
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $F$. Put $D=\bigcup_{x\in T} (\,\cdot\,*x)$-images of `centreCutSiegelSet F c u d₁ d₂`, the set of adelic matrices whose finite part is integral, whose archimedean component at each infinite place has local height at least $c$ and $x$-window square at most $u^2$, and whose archimedean determinant norm at each infinite place lies in $[d_1,d_2]$. Assume `CoversModCentre F D`: every adelic $g$ can be written with $\gamma\in\mathrm{GL}_2(F)$ and a central idelic scalar $z$ so that $\gamma g z\in D$. Let $\Phi$ be a Hecke eigensystem over $F$ with complex coefficients (a nonzero level ideal together with families $a,b$ indexed by the finite places), and assume `IsArithGenuineCuspRealizable` for $\Phi$ at the production pins attached to $D$, the level groups $N\mapsto$ `levelOne` at $N$ intersected with the kernel of the archimedean projection, the spherical generators `heckeGen`, and the adelic box. Let $\eta$ be a homomorphism from the idele units of $F$ to $\mathbb{C}^\times$ which is a finite-order Hecke character (trivial on principal global ideles, continuous, of finite order) and admits the modulus $\mathfrak f$, with $\mathfrak f\neq 0$; assume further that for every ideal $N$ and every finite place $v\nmid N$ the double coset of `heckeGen` at $v$ for the pins' level group at $N$ has a system of exactly $|\mathcal{O}_F/v|+1$ coset representatives. Then there exist a Hecke eigensystem $\Phi'$ over $F$ with complex coefficients and a finite set $S$ of finite places such that for all $v\notin S$ one has $\Phi'.a\,v=\eta(\det \mathrm{heckeGen}_v)\,\Phi.a\,v$ and $\Phi'.b\,v=\eta(\det \mathrm{heckeGen}_v)^2\,\Phi.b\,v$, and $\Phi'$ is again arithmetically genuinely cusp-realizable at the same pins. The proof visibly discards the hypotheses $\mathfrak f\neq 0$ and the coset-system hypothesis.
--
--   This is the eigensystem-level form of the classical fact that twisting a cuspidal automorphic representation of $\mathrm{GL}_2$ by a finite-order idele-class character again yields a cuspidal automorphic form, with the Satake parameters scaled by $\eta(\det)$ in the first Hecke coefficient and by its square in the second. It serves the Langlands–Tunnell input to the argument and is used in the derivation of the corresponding statement for ray class characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isArithGenuineCuspRealizable_twist_of_coversModCentre_centreCut.lean

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HeckeCharacter_FiniteOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open HeckeIntegralSeam

theorem LanglandsTunnell.exists_isArithGenuineCuspRealizable_twist_of_coversModCentre_centreCut
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Φ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    (hsys : ∀ (N : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)), ¬ v.asIdeal ∣ N →
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
        IsHeckeCosetSystem
          ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N)
          (heckeGen (𝓞 F) F v) reps) :
    ∃ Φ' : HeckeEigensystem F ℂ, ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      (∀ v ∉ S,
        Φ'.a v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) * Φ.a v ∧
        Φ'.b v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) ^ 2 * Φ.b v) ∧
      IsArithGenuineCuspRealizable F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
        Φ' := by sorry
