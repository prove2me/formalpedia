-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_blockQuadratic_colHarmonic_of_evenSheet
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_blockQuadratic_colHarmonic_of_evenSheet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/4c4152fb-109b-56a6-a5e5-d44ab49cef12
-- title:
--   Integrability of dual quadruple and torus-triple quadratic integrands
-- statement:
--   Let $\nu_1,\nu_2\in\mathbb{C}$, $b\in\mathbb{Z}/2$, and let $W:\mathbb{R}\to\mathbb{C}$ be continuous on $\{t\neq 0\}$ with $W(-t)=(-1)^{b}W(t)$ and, for $t>0$, $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_0^\infty r^{\nu_1+\mathrm{signShift}(b+b)}e^{-\pi r^2}(t/r)^{\nu_2+\mathrm{signShift}(b+b)}e^{-\pi(t/r)^2}\,dr/r$ (here $b+b=0$, so the shift `signShift (b+b)` is $0$). Let $P_2$ be a real archimedean parameter and $D$ an archimedean datum for $P_2$, i.e. a function $D.W$ on real $2\times2$ matrices satisfying the unipotent and central transformation laws attached to $P_2$ together with the smoothness, zeta-integral, functional-equation and decay conditions of `ArchDatumR`. Fix $a\in\mathbb{R}$, $a\neq 0$, $u_0,c_P\in\mathbb{C}$, $a_0,s_P\in\mathbb{Z}/2$, $n\in\mathbb{N}$ and $\delta\in\{0,1\}$. Then there is $\sigma\in\mathbb{R}$ such that for every $s$ with $\operatorname{Re} s>\sigma$ both of the following hold. (1) The function of $(x,t,q,p)$ given by $x^{2s-c_P-P_2.\mathrm{centralExponent}+n}e^{-\pi x^2q^2}$ times $\varepsilon_{s_P}(-t)\varepsilon_{a_0}(-t)\operatorname{sign}(t)\varepsilon_{n}(q)\varepsilon_{a_0}(q)$ (where $\varepsilon_\alpha(y)=$ `quasiChar 0 α y` is $1$ for $\alpha=0$ and $\operatorname{sign}(y)$ otherwise), times $W(-t)\cdot\bigl(p\operatorname{sign}(t)\bigr)\bigl(a^2\operatorname{sign}(t)(pq)^{-1}\bigr)^{\delta}\cdot\bigl(-t^2p^2+a^2p^{-2}+\tfrac1{2\pi}-a^2q^{-2}+2a|t|pq^{-1}\bigr)\cdot D.W(\mathrm{diagOne}(a|t|p/q))$, times $|t|^{s-5/2-c_P-P_2.\mathrm{centralExponent}}|q|^{u_0+n}p^{u_0-P_2.\mathrm{centralExponent}-3}$, times $e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$, is integrable on $(0,\infty)\times\mathbb{R}\times\mathbb{R}\times(0,\infty)$ for Lebesgue measure. (2) For all $b_0,\dots,b_4\in\mathbb{C}$, the analogous function of $(t,q,p)$, with the quadratic bracket replaced by $b_0t^2p^2+b_1a^2p^{-2}+b_2+b_3a^2q^{-2}+b_4a|t|pq^{-1}$ and the exponent of $|q|$ replaced by $u_0+c_P+P_2.\mathrm{centralExponent}-2s-1$, is integrable on $\mathbb{R}\times\mathbb{R}\times(0,\infty)$. Here $\mathrm{diagOne}(y)$ denotes the matrix $\begin{pmatrix}y&0\\0&1\end{pmatrix}$ and $P_2.\mathrm{centralExponent}$ is $u_1+u_2$ in the principal case and $2u$ in the discrete case.
--
--   This is the absolute-convergence input for the archimedean zeta computations of Stade type: it licenses the Fubini interchanges and the term-by-term evaluation of the four-variable dual integral and of the torus-triple integral with an arbitrarily weighted quadratic kernel. It is used in the Gamma-factor identity for the dual torus triple with quadratic kernel and harmonic column weight, and in the Rankin–Selberg identification of the dual torus pair with the archimedean root number times an explicit gamma factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_blockQuadratic_colHarmonic_of_evenSheet.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_blockQuadratic_colHarmonic_of_evenSheet
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun r : ℝ × ℝ × ℝ × ℝ =>
        (((r.1 : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + n) * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-r.2.1) * ArchR.quasiChar 0 a₀ (-r.2.1) * ArchR.quasiChar 0 1 r.2.1 * ArchR.quasiChar 0 (n : ZMod 2) r.2.2.1 * ArchR.quasiChar 0 a₀ r.2.2.1) *
          (W (-r.2.1) * (((((r.2.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 r.2.1) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 r.2.1 * (((r.2.2.2 * r.2.2.1)⁻¹ : ℝ) : ℂ)) ^ δ) *
              (-(((r.2.1 : ℝ) : ℂ) ^ 2 * ((r.2.2.2 : ℝ) : ℂ) ^ 2) + (a : ℂ) ^ 2 * ((r.2.2.2⁻¹ : ℝ) : ℂ) ^ 2 + 1 / (2 * (Real.pi : ℂ)) - (a : ℂ) ^ 2 * ((r.2.2.1⁻¹ : ℝ) : ℂ) ^ 2 + 2 * (a : ℂ) * ((|r.2.1| : ℝ) : ℂ) * ((r.2.2.2 : ℝ) : ℂ) * ((r.2.2.1⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |r.2.1| * r.2.2.2 / r.2.2.1))) *
          ((((|r.2.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|r.2.2.1| : ℝ) : ℂ) ^ (u₀ + n)) *
            (((r.2.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * r.2.1 ^ 2 * r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.1 ^ 2)) : ℂ)))) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) ∧
      ∀ b₀ b₁ b₂ b₃ b₄ : ℂ, Integrable (fun q : ℝ × ℝ × ℝ =>
        (ArchR.quasiChar 0 sP (-q.1) * ArchR.quasiChar 0 a₀ (-q.1) * ArchR.quasiChar 0 1 q.1 * ArchR.quasiChar 0 (n : ZMod 2) q.2.1 * ArchR.quasiChar 0 a₀ q.2.1) *
          (W (-q.1) * (((((q.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 q.1) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 q.1 * (((q.2.2 * q.2.1)⁻¹ : ℝ) : ℂ)) ^ δ) *
              (b₀ * (((q.1 : ℝ) : ℂ) ^ 2 * ((q.2.2 : ℝ) : ℂ) ^ 2) + b₁ * ((a : ℂ) ^ 2 * ((q.2.2⁻¹ : ℝ) : ℂ) ^ 2) + b₂ + b₃ * ((a : ℂ) ^ 2 * ((q.2.1⁻¹ : ℝ) : ℂ) ^ 2) + b₄ * ((a : ℂ) * ((|q.1| : ℝ) : ℂ) * ((q.2.2 : ℝ) : ℂ) * ((q.2.1⁻¹ : ℝ) : ℂ)))) * D.W (ArchR.diagOne (a * |q.1| * q.2.2 / q.2.1))) *
          ((((|q.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q.2.1| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((q.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * q.1 ^ 2 * q.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q.2.1 ^ 2)) : ℂ))) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
