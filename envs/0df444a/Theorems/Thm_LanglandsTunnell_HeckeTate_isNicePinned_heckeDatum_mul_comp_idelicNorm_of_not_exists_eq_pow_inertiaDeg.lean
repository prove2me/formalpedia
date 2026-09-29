-- Prove2me | Theorems.Thm_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum_mul_comp_idelicNorm_of_not_exists_eq_pow_inertiaDeg
-- name    : LanglandsTunnell.HeckeTate.isNicePinned_heckeDatum_mul_comp_idelicNorm_of_not_exists_eq_pow_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/a3780c0b-5020-5eb2-9ed4-4fc0eda68751
-- title:
--   Pinned functional equation for a non-normic character twisted from ℚ
-- statement:
--   Let $K$ be a number field, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra (this structure is what defines the prime $\mathfrak{P}\cap\mathbb{Q}$ under a prime $\mathfrak{P}$ of $\mathcal{O}_K$ and the inertia degree). Let $\mu$ be a character of the ideles of $K$ with values in $\mathbb{C}^\times$ which is an admissible twist, i.e. trivial on the principal ideles $K^\times$, continuous, and of absolute value $1$ everywhere. Assume $\mu$ is non-normic in the following sense: there is no admissible twist $\eta$ of the ideles of $\mathbb{Q}$ such that for every finite prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified (its local character is trivial on local units) and whose prime below has $\eta$ unramified, $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_{\mathfrak{P}\cap\mathbb{Q}})^{f}$, where $\varpi$ denotes the chosen uniformizer ideles and $f$ is the inertia degree. Let data $uR(w)\in\mathbb{C}$, $aR(w)\in\mathbb{Z}/2$ be given at the real places and $uC(w)\in\mathbb{C}$, $kC(w)\in\mathbb{Z}$ at the complex places, such that the archimedean component of $\mu$ at a real $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}(x/\|x\|)^{aR(w)^{\sharp}}$ (with $aR(w)^{\sharp}$ the integer representative of $aR(w)$) and at a complex $w$ is $x\mapsto\|x\|^{\mathrm{mult}(w)\,uC(w)}(x/\|x\|)^{kC(w)}$. Let $\tau$ be an admissible twist of the ideles of $\mathbb{Q}$, $t\in\mathbb{C}$ and $e\in\mathbb{Z}$ with archimedean component of $\tau$ at every real place of $\mathbb{Q}$ of the above shape with exponents $(t,e)$. Put $\chi=\mu\cdot(\tau\circ N)$, where $N$ is the idelic norm attached to the genuine base change of adeles from $\mathbb{Q}$ to $K$. Then the degree-one $L$-datum `heckeDatum` of $\chi$ formed with real parameters $(uR(w)+t,\;aR(w)+e \bmod 2)$ and complex parameters $(uC(w)+t,\;kC(w))$ — Euler factor $1-\chi(\varpi_v)X$ at the unramified $v$ and $1$ elsewhere, dual factor with $\chi(\varpi_v)^{-1}$, norms $\mathrm{N}v$, abscissa $1$, centre $1/2$, degree $1$ — is nicely pinned with trivial $S$-factors, root number $\varepsilon=$ `heckeRootNumber` of $\chi$ (formed from $aR+e$ and $kC$) and conductor $N=$ `heckeConductor` of $\chi$: the datum is well formed, its Euler product converges, $N>0$, and there exist entire functions $\Lambda,\Lambda^\vee$, bounded on vertical strips, which for $\operatorname{Re} s>1$ equal the archimedean factor times the $L$-function, respectively the dual archimedean factor times the dual $L$-function, and satisfy $\Lambda(s)=\varepsilon\,N^{1/2-s}\Lambda^\vee(1-s)$ for all $s$.
--
--   This is Hecke's analytic continuation and functional equation for the $L$-function of an idele class character of $K$, in the packaged form of a pinned $L$-datum, for the special class of characters obtained by twisting a non-normic character by the norm pull-back of a character of $\mathbb{Q}$. It feeds the cubic-induction step of the Langlands–Tunnell argument, where such twists arise from characters of the cubic extension attached to a projective representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum_mul_comp_idelicNorm_of_not_exists_eq_pow_inertiaDeg.lean

import Mathlib.NumberTheory.RamificationInertia.Basic
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open LanglandsTunnell.Converse LanglandsTunnell.HeckeTate

theorem LanglandsTunnell.HeckeTate.isNicePinned_heckeDatum_mul_comp_idelicNorm_of_not_exists_eq_pow_inertiaDeg
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hτ : IsAdmissibleTwist ℚ τ) (t : ℂ) (e : ℤ)
    (hτinf : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ τ v t e) :
    IsNicePinned
      (heckeDatum K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
        (fun w hw => uR w hw + t) (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC)
      (fun _ => 1) (fun _ => 1)
      (heckeRootNumber K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
        (fun w hw => aR w hw + (e : ZMod 2)) kC)
      (heckeConductor K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)) := by sorry
