-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_torusPair_rpow_det
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_torusPair_rpow_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/36a3b361-31ff-53e9-a3ee-d6f98686e5d7
-- title:
--   Half-plane integrability of archimedean GL₂timesGL₃ Rankin–Selberg integrands
-- statement:
--   Fix a real archimedean parameter $P$, either $\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ or $\mathrm{discrete}\,u_0\,n$ with $n\ge 1$, subject to the condition that in the principal case $|\mathrm{Re}(u_1-u_2)|<1$. Given weights $k:\mathbb Z/2\times\{\text{infinite places of }\mathbb Q\}\to\mathbb Z$, torus profiles $W_r^{\varepsilon}:\mathbb R\to\mathbb C$ and functions $W_A^{\varepsilon}$ on $\mathrm{GL}_2(\mathbb R)$, indexed by a parity $\varepsilon\in\mathbb Z/2$, assume: at every real place, $k^{\varepsilon}=\mathrm{signShift}(a_1+\varepsilon)+\mathrm{signShift}(a_2+\varepsilon)$ in the principal case (where $\mathrm{signShift}\,a$ is $0$ for $a=0$ and $1$ otherwise) and $k^{\varepsilon}=n+1$ in the discrete case; when $P=\mathrm{principal}\,u_1\,a_1\,u_2\,a_1$ and $\varepsilon=a_1$, $W_r^{\varepsilon}(-t)=(-1)^{a_1}W_r^{\varepsilon}(t)$; in the discrete case $W_r^{\varepsilon}$ vanishes on $t<0$; for $\varepsilon=a_1+1$ in the equal-parity principal case, the Mellin transform of $t\mapsto (W_r^{\varepsilon}(t)+(-1)^{a_1}W_r^{\varepsilon}(-t))/t$ converges in some right half-plane and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$; and for every $b\in\{\varepsilon,\varepsilon+P.\mathrm{centralSign}\}$ the same Mellin transform with $(-1)^{b}$ converges and equals the archimedean factor of $P$ twisted by $(0,b)$. Assume further that each $W_A^{\varepsilon}$ is continuous, satisfies $W_A^{\varepsilon}(\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)h)=e^{2\pi i x}W_A^{\varepsilon}(h)$, transforms under scalars $z\in\mathbb R^{\times}$ by $|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}}$, transforms on the right under the subgroup `rowIsometrySubgroup₀ ℝ` by the character `archWeightCharℝ` of weight $k^{\varepsilon}$ at the default place, and satisfies $W_A^{\varepsilon}(\mathrm{diag}(t,1))=W_r^{\varepsilon}(t)$. Let $w_{0}\in\mathrm{GL}_2(\mathbb R)$ have matrix $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$, and let $W$ be a continuous function on $\mathrm{GL}_3$ over the infinite adeles of $\mathbb Q$ for which there is $t\in\mathbb N$ such that for every $N$ there is $C$ with $\|W(g_\infty)\|\le C/\bigl((\prod_w \mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g))^{t}(1+\sum_w(\mathrm{archRoot}_1+\mathrm{archRoot}_2)(w,g))^{N}\bigr)$ for all adelic $g\in\mathrm{GL}_3$, $g_\infty$ its infinite-adelic component. Then for every parity $\varepsilon_0$ and every Haar measure $\mu_N$ on the upper unipotent subgroup $\{\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)\}$ of $\mathrm{GL}_2(\mathbb R)$ there is $\sigma_I\in\mathbb R$ such that, for all $s$ with $\mathrm{Re}\,s>\sigma_I$, both $g\mapsto W_A^{\varepsilon_0}(g)\,W\bigl(\iota(g)_\infty\bigr)|\det g|^{s-1/2}$ and $g\mapsto |\det g|\,W_A^{\varepsilon_0}(w_0\,{}^{t}g^{-1})\,W\bigl(w_3\,{}^{t}\iota(g)_\infty^{-1}\bigr)|\det g|^{s-1/2}$ are integrable on $\mathrm{GL}_2(\mathbb R)$, with its Borel $\sigma$-algebra, for the measure [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) (Lebesgue measure on $2\times2$ matrices with density $|\det g|^{-2}$) weighted by the orbit density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $\mu_N$; here $\iota(g)$ is $g$ placed at the real place of $\mathbb Q$ and embedded as the upper $2\times 2$ block in $\mathrm{GL}_3$, and $w_3$ is the long Weyl element of $\mathrm{GL}_3$.
--
--   This is the convergence statement for the archimedean $\mathrm{GL}_2\times\mathrm{GL}_3$ Rankin–Selberg integrals and its dual, derived from the unipotent, central, weight and Mellin laws of the $\mathrm{GL}_2$ datum together with the rapid decay of the $\mathrm{GL}_3$ Whittaker function in the root coordinates. It supplies the integrability side conditions of the archimedean assembly step which identifies the archimedean factor times the $L$-function of the Rankin–Selberg datum with an entire function bounded on vertical strips.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_torusPair_rpow_det.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_torusPair_rpow_det
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
        WA par (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * x) * WA par h)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])

    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (hWarch : (Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)))
    (par₀ : ZMod 2) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μN : MeasureTheory.Measure RSCarrier.realUnipotent) [μN.IsHaarMeasure],
    ∃ σI : ℝ,
      (∀ s : ℂ, σI < s.re → MeasureTheory.Integrable
        (fun g : GL (Fin 2) ℝ =>
          (WA par₀ g * Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))) *
            (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density RSCarrier.realUnipotent μN))) ∧
      (∀ s : ℂ, σI < s.re → MeasureTheory.Integrable
        (fun g : GL (Fin 2) ℝ =>
          ((((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv g)) *
              dualWhittakerFn3 Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))) *
            (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density RSCarrier.realUnipotent μN))) := by sorry
