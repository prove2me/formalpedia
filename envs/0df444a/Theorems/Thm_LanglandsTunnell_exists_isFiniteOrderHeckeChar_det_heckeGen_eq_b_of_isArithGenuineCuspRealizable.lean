-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable
-- name    : LanglandsTunnell.exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/d02eed34-59c6-5d5a-b920-8ecc77ea9338
-- title:
--   Determinant eigenvalues come from a finite-order Hecke character
-- statement:
--   Let $F$ be a number field, let $D$ be a set of points of the adelic group $\mathrm{GL}_2(\mathbb{A}_F)$, and let $\Phi$ be a complex Hecke eigensystem for $F$, that is, a nonzero level ideal of $\mathcal{O}_F$ together with two families $a_v, b_v \in \mathbb{C}$ indexed by the finite places $v$ of $F$. Assume `IsArithGenuineCuspRealizable` holds for $\Phi$ at the carrier pins `productionPinsOf` assembled from: the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the carrier $D$, the full group $\top$ as central subgroup, the level subgroups $N \mapsto$ `levelOne` at $N$ intersected with the kernel of the archimedean projection `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen` at each $v$, and the additive adelic Haar measure conditioned on the adelic box; by definition this asserts the existence of a term of `SmoothCuspRealizationAt` for the rescaled eigensystem `toRawCentral` $\Phi$, whose determinant entries are $(\mathrm{cNorm}\,v)^{-1} b_v$, satisfying `IsGenuineCuspRealizationAt`. Assume further that for some integer $n > 0$ there is a finite set of finite places outside which $b_v^{\,n} = 1$. Then there is a monoid homomorphism $\eta \colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ which is a finite-order Hecke character, i.e. trivial on the principal ideles, continuous and of finite order; which admits some nonzero ideal $\mathfrak{f}$ of $\mathcal{O}_F$ as a modulus, meaning $\eta(u) = 1$ whenever $u$ has trivial archimedean component, unit valuation at every finite place, and $v(u_v - 1) \le \exp(-\mathrm{ord}_v \mathfrak{f})$ for all $v$; and which satisfies $\eta(\det(\mathtt{heckeGen}\,v)) = b_v$ for all $v$ outside some finite set of finite places.
--
--   This is the passage from the determinant (central) eigenvalues of a cuspidal Hecke eigensystem on $\mathrm{GL}_2$ over a number field to an honest finite-order Hecke character of $F$ interpolating them at almost all finite places, the central character of the realisation corrected by the idelic absolute value. It feeds the base-change step [`LanglandsTunnell.exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH`](thm.html#LanglandsTunnell.exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH) in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable.lean

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

theorem LanglandsTunnell.exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Φ)
    (n : ℕ) (hn : 0 < n) (hbn : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, Φ.b v ^ n = 1) :
    ∃ η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, HeckeCharacter.IsFiniteOrderHeckeChar F η ∧
      (∃ 𝔣 : Ideal (𝓞 F), 𝔣 ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣) ∧
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) = Φ.b v := by sorry
