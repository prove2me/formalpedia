-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_twoSheet_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
-- name    : LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_integral_twoSheet_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/0d647ef0-0895-5bf2-87a1-589ece06b160
-- title:
--   Folded two-sheet Hermite formula for the degree-m archimedean zeta
-- statement:
--   Fix a nonzero $a\in\mathbb{Q}$ and an additive character $\psi_\infty$ of the infinite adele ring of $\mathbb{Q}$ with $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$ for all $x$. Let $D$ be an `ArchDatumR` for a real archimedean parameter $P_2$ (a real Whittaker datum: a function $W$ on $2\times2$ real matrices with the unipotent and central transformation laws, smoothness, zeta‑integrability, entire zeta function with functional equation and the stated growth and decay bounds), and let $k_0\in\mathbb{N}$ be such that $D.W(x r)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\cdot D.W(x)$ for all $r$ in `rowIsometrySubgroup₀ ℝ` and all $x\in GL_2(\mathbb{R})$. Let $u_3\in\mathbb{C}$, $a_3\in\mathbb{Z}/2$, let $m,n\in\mathbb{N}$ and $\varepsilon'\in\mathbb{R}$ satisfy either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$, and let $S$ on $2\times3$ real matrices be $S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^m\,(M_{02}+\varepsilon' i M_{12})^n\,e^{-\pi\sum_{i,b}M_{ib}^2}$. Let $\nu_{\mathrm{mul}}$ be a Haar measure on the units of the infinite adele ring whose push‑forward under the real coordinate is $\kappa$ times $|y|^{-1}\,dy$ on $\mathbb{R}$, let $\sigma$ be a character of the idele class units of $\mathbb{Q}$ whose archimedean component at every real place is $x\mapsto\|x\|^{0}\,(x/\|x\|)^e$ for some $e\in\mathbb{Z}$, and let $E$ be a homomorphism from the infinite ideles to the full ideles with infinite part the identity and trivial finite part. Then there is $\sigma_0\in\mathbb{R}$ such that for every $s$ with $\operatorname{Re}s>\sigma_0$ one has $\kappa>0$ and $$\mathrm{archZeta30}\,\nu_{\mathrm{mul}}\,\bigl(\mathrm{jacquetVector3}\,D\,u_3\,a_3\,a\,\psi_\infty\,S\bigr)\,(\sigma\circ E)\,s\,1=\kappa\cdot 2\pi(\varepsilon'a)^n\int_0^\infty y^{s-2}\!\!\iint_{(0,\infty)^2}\!\!\chi_{u_3+2,a_3}\bigl((y_1y_2)^{-1}\bigr)\,y_2^{\,n+2}\,\chi_{P_2}(y_2)\,e^{-\pi(y_1^{-2}+y_2^{-2}+a^2y_2^2+a^2y^2y_1^2)}\,B,$$ where $\chi_{u,a}(y)=|y|^{u}$ times the sign of $y$ when $a\neq0$, $\chi_{P_2}$ is the central quasi‑character of $P_2$, and, with $\tau=ayy_1/y_2$, $u=1/y_1$, $v=1/y_2$, $w=ayy_1$, $\mathrm{He}_m(t)=\int_{\mathbb{R}}e^{-\pi u'^2}(t+iu')^m\,du'$, $f_D(\tau)=D.W\bigl(\mathrm{diag}(\tau,1)\bigr)$ and $\bar e=e\bmod 2$, the bracket is $$B=f_D(\tau)\mathrm{He}_m(u-v-w)+(-1)^{a_3}f_D(-\tau)\mathrm{He}_m(-u-v+w)+(-1)^{\bar e}f_D(-\tau)\mathrm{He}_m(u-v+w)+(-1)^{\bar e+a_3}f_D(\tau)\mathrm{He}_m(-u-v-w).$$ Here $\mathrm{archZeta30}$ is the integral over the infinite ideles of the Whittaker value at $\iota(\mathrm{diag}(z,1))g$ times $\sigma(z)\|z\|^{s-1}$, evaluated at $g=1$.
--
--   This is the unfolding step in the archimedean Rankin–Selberg computation for $GL_3$: the zeta integral of the Jacquet vector attached to the flat section $S$ of degree $m$ is rewritten as an explicit triple integral over the positive octant, the two torus sheets $f_D(\pm\tau)$ being kept separate and no parity restriction being imposed on the Levi weight $k_0$ or the column data $(\varepsilon',n)$. It is the input to the subsequent identification of the same quantity as a finite sum of real Gamma factors times Mellin transforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_twoSheet_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_integral_twoSheet_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (k₀ : ℕ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (k₀ : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (m n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = (k₀ : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - k₀))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
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
    :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      0 < κ ∧
      archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
        (κ : ℂ) * (2 * (Real.pi : ℂ) * ((ε' : ℂ) * (a : ℂ)) ^ n) *
          ∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
            ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
              ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (n + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ y₂ *
                (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
                (D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ a₃.val * D.W (ArchR.diagOne (-((a : ℝ) * y * y₁ / y₂))) * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ (e : ZMod 2).val * D.W (ArchR.diagOne (-((a : ℝ) * y * y₁ / y₂))) * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ a₃.val * D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m)) := by sorry
