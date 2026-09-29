-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_Wr_mul_abs_cpow_mul_inv_sq
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_Wr_mul_abs_cpow_mul_inv_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/e495d823-71e8-5cfe-906e-8c7547022708
-- title:
--   Integrability of a real Whittaker torus profile against |t|^{s-1/2}t⁻²
-- statement:
--   Fix an archimedean parameter $P$ for $\mathrm{GL}_2/\mathbb{R}$, i.e. either $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or $P=\mathrm{discrete}(u,k)$ with $k\ge 1$; a family $W_r$ of functions $\mathbb{C}\to\mathbb{C}$ indexed by a parity in $\mathbb{Z}/2$ and an infinite place of $\mathbb{Q}$; and a family $W_A$ of functions $\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ indexed by a parity. The hypotheses are: (hWr1) if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and the parity equals $a_1$, then $W_r(-t)=(-1)^{a_1}W_r(t)$ at every real place; (hWr2) if $P$ is discrete, then $W_r$ vanishes on the negative reals; (hWr3) if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and the parity equals $a_1+1$, then for $\operatorname{Re}s$ large the Mellin integral of $t\mapsto (W_r(t)+(-1)^{a_1}W_r(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the $\Gamma$-factor of $P$ twisted by $(0,a_1)$ (exponents unchanged, parities shifted by $a_1$), that factor being the product of $\Gamma_{\mathbb{R}}(s+\mu)$ and $\Gamma_{\mathbb{C}}(s+\nu)$ over the associated multisets; (hWr4) for each parity and each $b$ equal to that parity or to it plus the central sign of $P$ ($a_1+a_2$, resp. $k+1$ mod $2$), the same Mellin integral with $(-1)^{b}$ converges for $\operatorname{Re}s$ large with value the $\Gamma$-factor of $P$ twisted by $(0,b)$; (hWAt) $W_A$ at the diagonal matrix $\mathrm{diag}(t,1)$, $t\in\mathbb{R}^\times$, equals $W_r$ at the default infinite place of $\mathbb{Q}$ evaluated at $t$; (hWAc) each $W_A$ is continuous. The conclusion, for a given parity $\varepsilon$, is that there exists $\sigma_0\in\mathbb{R}$ such that for every $s$ with $\operatorname{Re}s>\sigma_0$ the function $t\mapsto W_r^{\varepsilon}(t)\,|t|^{s-1/2}\,(t^2)^{-1}$ is Bochner integrable on $\mathbb{R}$ for Lebesgue measure.
--
--   This is the archimedean absolute-convergence estimate for the torus profile of a real Whittaker function, obtained from the stated Mellin laws in a right half-plane. It feeds the domination step for the unfolded torus-pair integrand, [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3), in the Rankin–Selberg part of the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_Wr_mul_abs_cpow_mul_inv_sq.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_Wr_mul_abs_cpow_mul_inv_sq
    (P : RealArchParam)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
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
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (par₀ : ZMod 2) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      MeasureTheory.Integrable
        (fun t : ℝ => Wr par₀ default t * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by sorry
