-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_twoSheet_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
-- name    : LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_twoSheet_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/25f69c4d-c962-53ec-af70-4a21c5ae91af
-- title:
--   Hermite expansion of the archimedean GL₃ zeta integral
-- statement:
--   Fix a nonzero rational $a$ and an additive character $\psi_\infty$ of the infinite adele ring of $\mathbb{Q}$ with $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$. Let $D$ be an `ArchDatumR` for a real archimedean parameter $P_2$ — a Whittaker function $W$ on $2\times 2$ real matrices, smooth on the invertible locus, with the unipotent law $W(\mathrm{unip}(x)g)=\psi(x)W(g)$, the central law governed by `centralChar` $P_2$, an entire completed zeta function satisfying a functional equation and growth bounds, together with decay estimates — and suppose $W$ satisfies $W(x r)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(r)\,W(x)$ for $r$ in the row-isometry subgroup (those $r$ with $|\det r|=1$ preserving the quadratic form on row vectors). Let $u_3\in\mathbb{C}$, $a_3\in\mathbb{Z}/2$, let $m,n\in\mathbb{N}$ and $\varepsilon'\in\mathbb{R}$ satisfy either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$, and let $S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^m (M_{02}+\varepsilon' i M_{12})^n e^{-\pi\sum_{i,b}M_{ib}^2}$ on $2\times 3$ real matrices. Let $\nu_{\mathrm{mul}}$ be a Haar measure on the units of the infinite adele ring whose push-forward along the real coordinate is $\kappa\cdot|y|^{-1}dy$; let $\sigma$ be a character of the idele units with archimedean component at every real place of exponent $0$ and twist $e\in\mathbb{Z}$, and $E$ a monoid homomorphism splitting the infinite part, with $\mathrm{finPart}(E u)=1$. Define, for $j\in\mathbb{N}$ and $b\in\mathbb{Z}/2$, $$H_j^{(b)}(\sigma')=e^{-\pi a^2\sigma'^2}\int_0^\infty\bigl[W(\mathrm{diag}(a\sigma'/w,1))+(-1)^{b}W(\mathrm{diag}(-a\sigma'/w,1))\bigr]\,\mathrm{centralChar}(P_2)(w)\,|w|\,w^{\,n-u_3-1-j}e^{-\pi(w^{-2}+a^2w^2)}\,dw.$$ Then there is $\sigma_0\in\mathbb{R}$ such that for every $s$ with $\mathrm{Re}\,s>\sigma_0$: for each quadruple $T=((r,i),(j,l))$ with entries in $\{0,\dots,m\}$ subject to $i+j+l+2r=m$ and $i\equiv e+a_3 \pmod 2$, the Mellin transform of $H_j^{(e+l)}$ converges at $s+l-1$, and the archimedean zeta integral `archZeta30` of the Jacquet vector $\mathrm{jacquetVector3}(D,u_3,a_3,a,\psi_\infty,S)$ against $\sigma\circ E$ at $s$ and the identity equals $$\kappa\cdot 2\pi(\varepsilon' a)^n\sum_T(-1)^{j+l}\frac{(-1)^r\,m!\,a^{l}}{r!\,i!\,j!\,l!\,(4\pi)^r}\,\Gamma_{\mathbb R}(s+u_3+i)\,\mathcal{M}H_j^{(e+l)}(s+l-1),$$ the sum running over the same finite index set.
--
--   This is the explicit evaluation of the archimedean $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integral of the degree-$m$ flat Jacquet vector as a finite Hermite-type sum of products $\Gamma_{\mathbb R}(s+u_3+i)\,\mathcal{M}H_j^{(b)}(s+l-1)$, valid for an arbitrary $SO_2$-weight $k_0$ with column data $(\varepsilon',n)$ matched to it. It feeds the non-vanishing statements for the weight-zero, weight-one and discrete-series Levi branches used in the cubic-induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_twoSheet_of_conjBlockHarmonic_pow_colHarmonic_gaussian3.lean

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

open NumberField AutomorphicForm LanglandsTunnell.Converse
open LanglandsTunnell
open LanglandsTunnell.CubicInduction MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_sum_GammaR_mul_mellin_twoSheet_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
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
    (H : ℕ → ZMod 2 → ℝ → ℂ)
    (hH : ∀ (j : ℕ) (b : ZMod 2), H j b = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-((a : ℝ) * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ((n : ℂ) - u₃ - 1 - (j : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      (∀ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2) = (e : ZMod 2) + a₃)),
        MellinConvergent (H T.2.1 ((e : ZMod 2) + (T.2.2 : ZMod 2))) (s + (T.2.2 : ℂ) - 1)) ∧
      archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
        (κ : ℂ) * (2 * (Real.pi : ℂ) * ((ε' : ℂ) * (a : ℂ)) ^ n) *
          ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2) = (e : ZMod 2) + a₃)),
            ((-1 : ℂ) ^ (T.2.1 + T.2.2) *
              ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
                ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                  (4 * (Real.pi : ℂ)) ^ T.1.1))) *
              Complex.Gammaℝ (s + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1 ((e : ZMod 2) + (T.2.2 : ZMod 2))) (s + (T.2.2 : ℂ) - 1) := by sorry
