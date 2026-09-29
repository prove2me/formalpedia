-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_archWhittaker_w0R_mul_transposeInv_upperUnit_eq_mul_archProfile
-- name    : LanglandsTunnell.RankinSelberg.archWhittaker_w0R_mul_transposeInv_upperUnit_eq_mul_archProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/e8f61679-a21f-516e-bf1e-31006fcd94b1
-- title:
--   Archimedean Whittaker value at a reflected dual torus point
-- statement:
--   Fix a rational number $a$ and a real archimedean parameter $P$, i.e. either `RealArchParam.principal u₁ a₁ u₂ a₂` with $u_1,u_2\in\mathbb C$ and $a_1,a_2\in\mathbb Z/2$, or `RealArchParam.discrete u₀ n` with $n\ge 1$; it is assumed that in the principal case $|\mathrm{Re}(u_1-u_2)|<1$. Let $kw$ attach an integer to each parity in $\mathbb Z/2$ and each infinite place of $\mathbb Q$, let $Wr$ attach a function $\mathbb C\to\mathbb C$ to each parity and place, and let $WA$ attach a function on $GL_2(\mathbb R)$ to each parity, subject to the following laws. Weights: in the principal case $kw(\varepsilon,w)=\mathrm{signShift}(a_1+\varepsilon)+\mathrm{signShift}(a_2+\varepsilon)$ at real $w$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$, and in the discrete case $kw(\varepsilon,w)=n+1$. Profile: at real places, when $P$ is principal with $a_1=a_2$ and $\varepsilon=a_1$ one has $Wr(\varepsilon,w,-t)=(-1)^{a_1}Wr(\varepsilon,w,t)$; in the discrete case $Wr(\varepsilon,w,t)=0$ for $t<0$; and in two further cases (principal with $\varepsilon=a_1+1$, and $b\in\{\varepsilon,\varepsilon+s(P)\}$ with $s(P)=P.\mathrm{centralSign}$) the function $t\mapsto (Wr(\varepsilon,w,t)+(-1)^{b}Wr(\varepsilon,w,-t))/t$ is Mellin convergent in a right half plane with Mellin transform $(2s+u_1+u_2-1)/(4\pi)\cdot (P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$, respectively $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$, the archimedean Gamma factor attached to the indicated twist of $P$. Whittaker laws: $WA(\varepsilon,\cdot)$ satisfies $WA(\varepsilon,\begin{pmatrix}1&x\\0&1\end{pmatrix}h)=e^{-2\pi i a x}WA(\varepsilon,h)$; $WA(\varepsilon,zh)=|z|^{c(P)+1}(z/|z|)^{s(P)}WA(\varepsilon,h)$ for scalar $z\in\mathbb R^\times$, with $c(P)=P.\mathrm{centralExponent}$; $WA(\varepsilon,h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(kw(\varepsilon,\mathrm{default}))(\kappa)\,WA(\varepsilon,h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; $WA(\varepsilon,\mathrm{diag}(t,1))=Wr(\varepsilon,\mathrm{default},t)$ for $t\in\mathbb R^\times$; and $WA(\varepsilon,\cdot)$ is continuous. Let $w_0\in GL_2(\mathbb R)$ have matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Then for every parity $\varepsilon$, every $a_1\ne 0$ and every $a_2>0$, writing $q$ for the element of $GL_2(\mathbb R)$ with matrix $\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$ and ${}^tq^{-1}$ for the transpose of its inverse,
--   $$WA(\varepsilon,\;w_0\,{}^tq^{-1})=i^{\,kw(\varepsilon,\mathrm{default})}\cdot\bigl|-a_1^{-1}\bigr|^{c(P)+1}\Bigl(\tfrac{-a_1^{-1}}{|-a_1^{-1}|}\Bigr)^{s(P)}\cdot Wr(\varepsilon,\mathrm{default},-a_1/a_2).$$
--
--   This is the reflection law for the archimedean Whittaker function of a $GL_2$ datum over $\mathbb Q$: the value at the dual torus point $w_0\,{}^tq^{-1}$ is a single torus value of the radial profile $Wr$, with an explicit fourth-root-of-unity factor $i^{k}$ and the central character factor. It feeds the dual unfolding of the archimedean Rankin–Selberg integral, and is cited by the computations of the dual torus pairing for discrete-series and even principal-series parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_archWhittaker_w0R_mul_transposeInv_upperUnit_eq_mul_archProfile.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.archWhittaker_w0R_mul_transposeInv_upperUnit_eq_mul_archProfile
    (a : ℚ)
    (P : RealArchParam)
    (_hP₁ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (kw : ZMod 2 → InfinitePlace ℚ → ℤ)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hkw1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par) + signShift (a₂ + par))
    (hkw2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (hWAN : ∀ par : ZMod 2, ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA par (unipotentGL2 x * h) = Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ) * x)) * WA par h)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
    (par : ZMod 2) (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : 0 < a₂) :
    WA par (w₀R * RSCarrier.transposeInv (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne')) =
      Complex.I ^ (kw par default) *
        ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
          ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) *
        Wr par default (-a₁ / a₂) := by sorry
