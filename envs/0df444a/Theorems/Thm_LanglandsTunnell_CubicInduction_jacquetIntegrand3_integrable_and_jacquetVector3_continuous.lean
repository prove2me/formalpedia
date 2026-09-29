-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetIntegrand3_integrable_and_jacquetVector3_continuous
-- name    : LanglandsTunnell.CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/f012823c-e7aa-5456-a70b-1025f33439ff
-- title:
--   Integrability and continuity of the GL₃ Jacquet vector
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and $\mu$ a character of the idele units of $K$ valued in $\mathbb{C}^\times$ which is admissible, i.e. trivial on the image of $K^\times$, continuous and of absolute value $1$ everywhere. Let $u_w\in\mathbb{C}$, $a_w\in\mathbb{Z}/2$ be given at the real places and $u_w\in\mathbb{C}$, $k_w\in\mathbb{Z}$ at the complex places, with the hypotheses that at each infinite place the local component of $\mu$ on $(K_w)^\times$ is $x\mapsto \|x\|^{\,\mathrm{mult}(w)\,u_w}\,(x/\|x\|)^{a_w}$, resp. $(x/\|x\|)^{k_w}$; let $\omega$ be a character of the idele units of $\mathbb{Q}$ whose components at the real places are of the same shape with exponent $\sum_w u_w+\sum_{w\ \mathrm{cplx}}2u_w$ and integer $\sum_w a_w+\sum_{w\ \mathrm{cplx}}(k_w+1)$ (finite sums over the places), and let $E$ be a homomorphism from the infinite idele units of $\mathbb{Q}$ to the idele units splitting the infinite part and having trivial finite part. Let $a\in\mathbb{Q}$, $a\neq 0$, let $a_\infty$ be a unit of the infinite adeles with underlying element $a$, let $\psi_\infty$ be the additive character $x\mapsto \psi_{\mathrm{arch}}(ax)$ of the infinite adeles of $\mathbb{Q}$, let $\nu_{\mathrm{add}}$ be $|a|^{1/2}$ times the transport of Lebesgue measure along the mixed-space identification, and $\nu_{\mathrm{mul}}$ a Haar measure on the infinite idele units (with the attendant Borel measurable structures). Let $w_0$ be a real place of $K$ and $P_2$ a real archimedean parameter such that either $K$ has exactly the three distinct real places $w_0,w_1,w_2$ and $P_2$ is the principal parameter attached to $(u_{w_1},a_{w_1},u_{w_2},a_{w_2})$, or $K$ has exactly the places $w_0$ and a complex place $w_C$ and $P_2$ is the discrete parameter of weight $|k_{w_C}|$ with exponent $u_{w_C}$ when $k_{w_C}\neq 0$, resp. the principal parameter $(u_{w_C},0,u_{w_C},1)$ when $k_{w_C}=0$. Finally let $D$ be an `ArchDatumR` for $P_2$, that is a function $W$ on real $2\times2$ matrices, smooth on the invertible locus, with the unipotent and central transformation laws, an entire zeta function with the stated integral representation, functional equation and finite order, and the two decay estimates, and let $S$ lie in `polyGauss3`, i.e. $S(M)=p(M)\,\cdot\,\mathrm{gaussian3}(M)$ for a complex polynomial $p$ in the six entries of a real $2\times3$ matrix. Then for every $g\in \mathrm{GL}_3$ of the infinite adeles of $\mathbb{Q}$ the function $e\mapsto \mathrm{godementInner3}(\psi_\infty,S,e,g)\cdot \mathrm{quasiChar}(u_{w_0}+2,a_{w_0})(\det e)\cdot|\det e|^{-2}\cdot D.W(\mathrm{diagOne}(a)\,e^{-1})$ is Lebesgue integrable on real $2\times2$ matrices, and the function $g\mapsto \mathrm{quasiChar}(u_{w_0}+1,a_{w_0})(\det g_\infty)\int_e(\cdots)\,de$ given by `jacquetVector3` is continuous on $\mathrm{GL}_3$. Only $D$, $u_{w_0}$, $a_{w_0}$, $a$, $\psi_\infty$ and $S$ occur in the conclusion.
--
--   This is the absolute convergence of the archimedean Jacquet integral which produces a Whittaker vector on $\mathrm{GL}_3(\mathbb{R})$ from a $\mathrm{GL}_2(\mathbb{R})$ Whittaker datum and a polynomial-times-Gaussian section on $2\times3$ matrices, together with continuity of the resulting function of the group variable. It is used in the analysis of the zeta integrals of the same vector and in the packaging of its analytic properties, namely by [`LanglandsTunnell.CubicInduction.isKFinite_jacquetVector3`](thm.html#LanglandsTunnell.CubicInduction.isKFinite_jacquetVector3) and [`LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package`](thm.html#LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetIntegrand3_integrable_and_jacquetVector3_continuous.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.jacquetIntegrand3_integrable_and_jacquetVector3_continuous
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) :
    (∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ),
      MeasureTheory.Integrable
        (jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S g) MeasureTheory.volume) ∧
    Continuous
      (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) := by sorry
