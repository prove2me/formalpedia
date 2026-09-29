-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_archWhittaker_profile_eq_zero_and_eq_two_mul_cpow_mul_exp_of_discrete
-- name    : LanglandsTunnell.RankinSelberg.archWhittaker_profile_eq_zero_and_eq_two_mul_cpow_mul_exp_of_discrete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/13f597c2-5e41-5a01-8c7c-9f44ea4cdbad
-- title:
--   One-sided Whittaker profile for a discrete-series archimedean parameter
-- statement:
--   Let $P$ be a real archimedean parameter which is of discrete type, say $P = \mathrm{discrete}\,(u_P, n_P)$ with $u_P \in \mathbb{C}$ and $n_P \ge 1$ a natural number. Let $W_r$ assign to each parity $\varepsilon \in \mathbb{Z}/2$ and each infinite place $w$ of $\mathbb{Q}$ a function $\mathbb{C} \to \mathbb{C}$, and let $W_A$ assign to each parity a function on $\mathrm{GL}_2(\mathbb{R})$. Four hypotheses are imposed: (i) for every parity, every real place $w$, and every presentation of $P$ as $\mathrm{discrete}\,(u_0,n)$ with $n \ge 1$, one has $W_r^{\varepsilon}(w,t) = 0$ for all real $t < 0$; (ii) for every parity $\varepsilon$, every real place $w$ and every $b \in \mathbb{Z}/2$ with $b = \varepsilon$ or $b = \varepsilon + P.\mathrm{centralSign}$ (the latter being $n_P + 1 \bmod 2$ for a discrete parameter), there is $s_0 \in \mathbb{R}$ such that for $\operatorname{Re} s > s_0$ the Mellin integral of $t \mapsto (W_r^{\varepsilon}(w,t) + (-1)^{b}W_r^{\varepsilon}(w,-t))/t$ converges and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$, i.e. the product of $\Gamma_{\mathbb{R}}(s+\mu)$ over the real Gamma-shifts (empty for a discrete parameter) times the product of $\Gamma_{\mathbb{C}}(s+\nu)$ over the complex ones; (iii) for each parity and each real unit $t$, $W_A^{\varepsilon}(\mathrm{diag}(t,1)) = W_r^{\varepsilon}(w_\infty, t)$, where $w_\infty$ is the distinguished infinite place of $\mathbb{Q}$; (iv) each $W_A^{\varepsilon}$ is continuous. Then for the given parity $\varepsilon_0$ the profile at $w_\infty$ satisfies $W_r^{\varepsilon_0}(t) = 0$ for $t < 0$ and $W_r^{\varepsilon_0}(t) = 2\,t^{\,u_P + n_P/2 + 1} e^{-2\pi t}$ for $t > 0$.
--
--   This is the explicit determination of the archimedean Whittaker profile of a discrete-series $\mathrm{GL}_2$ parameter at the real place of $\mathbb{Q}$: the function is supported on the positive half-line and is there given by the classical Bessel-free formula $2t^{u+n/2+1}e^{-2\pi t}$. It supplies the positivity and vanishing properties of the profile used in the Rankin–Selberg unfolding step that matches the unfolded and dual torus integrals against the expected $\Gamma$-factor for a discrete-series parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_archWhittaker_profile_eq_zero_and_eq_two_mul_cpow_mul_exp_of_discrete.lean

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

theorem LanglandsTunnell.RankinSelberg.archWhittaker_profile_eq_zero_and_eq_two_mul_cpow_mul_exp_of_discrete
    (P : RealArchParam) (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hPdisc : P = RealArchParam.discrete uP nP hnP)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (par₀ : ZMod 2) :
    (∀ t : ℝ, t < 0 → Wr par₀ default t = 0) ∧
    (∀ t : ℝ, 0 < t → Wr par₀ default t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ)) := by sorry
