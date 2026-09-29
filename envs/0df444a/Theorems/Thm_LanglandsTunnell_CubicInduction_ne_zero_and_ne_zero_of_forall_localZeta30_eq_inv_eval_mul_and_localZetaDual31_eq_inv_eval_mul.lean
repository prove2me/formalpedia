-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_ne_zero_and_ne_zero_of_forall_localZeta30_eq_inv_eval_mul_and_localZetaDual31_eq_inv_eval_mul
-- name    : LanglandsTunnell.CubicInduction.ne_zero_and_ne_zero_of_forall_localZeta30_eq_inv_eval_mul_and_localZetaDual31_eq_inv_eval_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/9a48503f-8d4a-5d0f-ad0b-2c64bd503e2d
-- title:
--   Non-vanishing of the local Euler polynomials E and E^∨
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, write $N=\mathrm{absNorm}(v)$ and $\mathbb{Q}_v$ for the completion, and let $W:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ be a function with: $W(\mathrm{upperUnipotent}_3(x,y,z)\,g)=\psi_v^{-1}(x+y)\,W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $\psi_v$ is the standard local additive character `psiLocal ℚ v`; $W\neq0$; every nonzero $F$ lying in the $\mathbb{C}$-span of the right translates of $W$ has $W$ in the span of its own right translates; and $W$ is invariant under right multiplication by the elements of some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$. Let $E,E^{\vee}\in\mathbb{C}[X]$, $\varepsilon\in\mathbb{C}$ and $\ell\in\mathbb{N}$, and assume that for every $g\in\mathrm{GL}_3(\mathbb{Q}_v)$ there are a function $P:\mathbb{C}\to\mathbb{C}$ and reals $\sigma_0,\sigma_1$ such that: $P$ is rational in $N^{-s}$, i.e. there are $Q,R\in\mathbb{C}[X]$ with $R\neq0$ and $m\in\mathbb{N}$ with $P(s)R(N^{-s})=Q(N^{-s})N^{ms}$ for all $s$; the integrand $a\mapsto W(\mathtt{iotaGL}(\mathtt{diagUnitGL2}\,a)\,g)\,|a|^{s-1}$ is integrable for $\operatorname{Re}s>\sigma_0$ against the multiplicative measure $\mathtt{comap}\,(\mathtt{mulMeasure}\,(\mathtt{selfDualHaarAt}\ \mathbb{Q}\ v))$ on $\mathbb{Q}_v^{\times}$, with `localZeta30` for the trivial character equal to $E(N^{-s})^{-1}P(s)$ there; and the corresponding $(3,1)$ integrand for $\mathtt{dualWhittakerFn3}\,W$ at $\mathtt{weylPrime3}\cdot{}^{t}g^{-1}$ is integrable for $\operatorname{Re}s>\sigma_1$, with $\mathtt{localZetaDual31}(1-s,W,\mathbf 1;g)=E^{\vee}(N^{-(1-s)})^{-1}\bigl(\varepsilon N^{\ell(1/2-s)}P(s)\bigr)$ whenever $\sigma_1<\operatorname{Re}(1-s)$. Then $E\neq0$ and $E^{\vee}\neq0$.
--
--   This is the non-degeneracy of the Euler data in the translate-wise local functional equation for $\mathrm{GL}_3\times\mathrm{GL}_1$ at a finite place: the denominators produced by the local theory cannot be the zero polynomial. It is used in the construction of the dual middle datum for the local Rankin–Selberg integrals attached to a cubic induction, where $E$ and $E^{\vee}$ must be inverted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_ne_zero_and_ne_zero_of_forall_localZeta30_eq_inv_eval_mul_and_localZetaDual31_eq_inv_eval_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal MeasureTheory LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.ne_zero_and_ne_zero_of_forall_localZeta30_eq_inv_eval_mul_and_localZetaDual31_eq_inv_eval_mul
    (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    (hW0 : W ≠ 0)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))) :
    E ≠ 0 ∧ Ed ≠ 0 := by sorry
