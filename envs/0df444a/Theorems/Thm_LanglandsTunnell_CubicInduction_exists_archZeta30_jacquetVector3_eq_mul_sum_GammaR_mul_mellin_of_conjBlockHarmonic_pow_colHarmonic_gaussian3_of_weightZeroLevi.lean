-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
-- name    : LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/6f617718-6c35-51ab-ac37-036d39044a9c
-- title:
--   Explicit Hermite sum for a degree-m archimedean GL₃ zeta integral
-- statement:
--   Fix a nonzero rational $a$ and an additive character $\psi_\infty$ of the infinite adele ring of $\mathbb{Q}$ of the form $\psi_\infty(x)=\psi_{\mathrm{arch}}(a\,x)$. Let $D$ be an archimedean Whittaker datum `ArchDatumR` for a real parameter $P_2$ — a function $W$ on $2\times 2$ real matrices, smooth on the invertible locus, with unipotent law $W(\mathrm{unip}(x)g)=\psi(x)W(g)$, central law governed by `centralChar` $P_2$, entire zeta functions satisfying a functional equation with $\varepsilon$-factor `epsilonFactor`, finite order in vertical strips and the stated decay bounds — and assume $W$ is right invariant under `rowIsometrySubgroup₀ ℝ`. Let $u_3\in\mathbb{C}$, $a_3\in\mathbb{Z}/2$, $m\ge 1$, and let $S$ be the section $S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^m (M_{02}+iM_{12})^m\exp\bigl(-\pi\sum_{i,b}M_{ib}^2\bigr)$ on $2\times 3$ real matrices. Assume $P_2=\mathrm{principal}(u_1,c,u_2,c)$ and the torus parity $W(\mathrm{diagOne}(-\tau))=(-1)^{c}W(\mathrm{diagOne}(\tau))$ for $\tau\neq0$. Let $\nu_{\mathrm{mul}}$ be a Haar measure on the units of the infinite adele ring whose push-forward under the real coordinate is $\kappa$ times Lebesgue measure with density $|y|^{-1}$. Let $\sigma$ be a character of the idele units whose local component at every real infinite place is $x\mapsto (x/|x|)^{e}$ in the sense of `IsArchCompAt` with exponent $0$ and twist $e$, and let $E$ be a homomorphism from the infinite adele units to the idele units with infinite part the identity and finite part $1$. Let $H_j(\sigma')=e^{-\pi a^2\sigma'^2}\int_0^\infty W(\mathrm{diagOne}(a\sigma'/w))\,\mathrm{centralChar}\,P_2(w)\,|w|\,w^{\,m-u_3-1-j}e^{-\pi(w^{-2}+a^2w^2)}\,dw$. Then there is $\sigma_0\in\mathbb{R}$ such that for all $s$ with $\operatorname{Re}s>\sigma_0$: for every quadruple $T=((r,i),(j,l))$ with entries in $\{0,\dots,m\}$ satisfying $i+j+l+2r=m$, $j\equiv a_3+c+m$ and $l\equiv e+c$ modulo $2$, the Mellin transform of $H_j$ converges at $s+l-1$; and the zeta integral `archZeta30`, namely $\int W_J(\mathrm{iotaGL}(\mathrm{diagUnitGL2}\,\alpha))\,\sigma(E\alpha)\,\|\alpha\|^{s-1}\,d\nu_{\mathrm{mul}}(\alpha)$ with $W_J=\mathrm{jacquetVector3}\,D\,u_3\,a_3\,a\,\psi_\infty\,S$ (the product of $\mathrm{quasiChar}(u_3+1,a_3)$ of the determinant with the integral over $2\times2$ real matrices $\epsilon$ of $\mathrm{godementInner3}\,\psi_\infty\,S\,\epsilon$ against $\mathrm{quasiChar}(u_3+2,a_3)(\det\epsilon)\,|\det\epsilon|^{-2}\,W(\mathrm{diagOne}(a)\epsilon^{-1})$), evaluated at the identity, equals $$\kappa\cdot 4\pi\,(-1)^{a_3+m+e}a^m\sum_T \frac{(-1)^r\,m!\,a^{l}}{r!\,i!\,j!\,l!\,(4\pi)^r}\,\Gamma_{\mathbb{R}}(s+u_3+i)\,\mathcal{M}H_j(s+l-1),$$ the sum over the same set of quadruples.
--
--   This is the explicit archimedean computation, in the weight-zero principal Levi branch, of the $GL_3\times GL_1$ zeta integral attached to the degree-$m$ flat section: the answer is a finite Hermite-type sum of products $\Gamma_{\mathbb{R}}(s+u_3+i)\,\mathcal{M}H_j(s+l-1)$ supported on an explicit parity class. It feeds the construction of an admissible twist for which this archimedean zeta integral is nonvanishing, part of the converse-theorem input to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (m : ℕ) (hm : 1 ≤ m)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ m) * gaussian3 M)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (H : ℕ → ℝ → ℂ)
    (hH : ∀ j : ℕ, H j = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ((m : ℂ) - u₃ - 1 - (j : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      (∀ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c)),
        MellinConvergent (H T.2.1) (s + (T.2.2 : ℂ) - 1)) ∧
      archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
        (κ : ℂ) * (4 * (Real.pi : ℂ)) * (-1 : ℂ) ^ ((a₃ + (m : ZMod 2) + (e : ZMod 2)).val) * (a : ℂ) ^ m *
          ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
              (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c)),
            ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
                ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                  (4 * (Real.pi : ℂ)) ^ T.1.1)) *
              Complex.Gammaℝ (s + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1) (s + (T.2.2 : ℂ) - 1) := by sorry
