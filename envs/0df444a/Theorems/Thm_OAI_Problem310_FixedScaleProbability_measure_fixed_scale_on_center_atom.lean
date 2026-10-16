-- Prove2me | Theorems.Thm_OAI_Problem310_FixedScaleProbability_measure_fixed_scale_on_center_atom
-- name    : OAI.Problem310.FixedScaleProbability.measure_fixed_scale_on_center_atom
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:49:12.023898+00:00
-- url     : https://prove2.me/theorems/98a691ac-a843-41ba-961c-b4ddf5e24f19
-- title:
--   Exact fixed-scale failure probability on a center-exposure atom
-- statement:
--   Let $C,I,S,T$ be finite sets: $S$ indexes selector coordinates, $T$ terminal coordinates, $C$ the exposed center coordinates and $I$ the fresh trials. Bits are written $0$ (false) and $1$ (true). Let $\nu_s,\nu_t$ be probability measures on $\{0,1\}$ with $\nu_s\{0\}=\nu_s\{1\}=\tfrac12$ and $\nu_t\{0\}=1-p$ for a real number $p\le 1$ (as $\nu_t$ is a probability measure, this forces $0\le p\le 1$ and $\nu_t\{1\}=p$). Let $\mathbb{P}=\nu_s^{\otimes S}\otimes\nu_t^{\otimes T}$ be the law of a pair $(a,\tau)$ of independent random tables $a\in\{0,1\}^S$ (i.i.d. fair bits) and $\tau\in\{0,1\}^T$ (i.i.d. bits equal to $1$ with probability $p$).
--
--   Let $\mathrm{center}:C\to S$ and $\mathrm{fresh}:I\to S$ be such that the combined map on the disjoint union $C\sqcup I$ is injective (all center and fresh coordinates are distinct), let $\mathrm{value}:C\to\{0,1\}$ prescribe the exposed center bits, and let $\mathrm{addr}:\{0,1\}^S\times I\to T$ choose the terminal coordinate of each trial, possibly depending on the whole selector table, such that $\mathrm{addr}(a,\cdot)$ is injective for every $a$. Consider the event that the center exposure equals $\mathrm{value}$ and every active trial fails:
--
--   $$F=\Big\{(a,\tau):\ a(\mathrm{center}(c))=\mathrm{value}(c)\ \text{ for all } c\in C,\ \text{ and }\ \tau(\mathrm{addr}(a,i))=0\ \text{ for every } i\in I \text{ with } a(\mathrm{fresh}(i))=1\Big\}.$$
--
--   **Theorem.** Under these assumptions,
--
--   $$\mathbb{P}(F)=\Big(\prod_{c\in C}\nu_s\{\mathrm{value}(c)\}\Big)\cdot\Big(1-\frac p2\Big)^{|I|}.$$
--
--   Conditionally on the exposure atom, each fresh trial is active with probability $\tfrac12$ independently of the others, and an active trial fails with probability $1-p$ independently of everything else, even though the terminal coordinate it reads may depend on all selector bits. This is the finite-product form of the conditional miss estimate at one fixed scale.
--
--   **Formalization Note** The measure is `(Measure.pi (fun _ : S => νs)).prod (Measure.pi (fun _ : T => νt))` and takes values in $[0,\infty]$; the hypotheses on $\nu_s$ are `νs {false} = 1 / 2` and `νs {true} = 1 / 2`, and the one on $\nu_t$ is `νt {false} = ENNReal.ofReal (1 - p)` with `p ≤ 1`. The factor $1-p/2$ appears as `ENNReal.ofReal (1 - p / 2)`. Distinctness of center and fresh coordinates is `Function.Injective (Sum.elim center fresh)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/FixedScaleProbability.lean#L64-L97

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses

open OAI OAI.Problem310
universe u_A u_I u_K u_C u_S u_T
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem OAI.Problem310.FixedScaleProbability.measure_fixed_scale_on_center_atom
    {C : Type u_C} {I : Type u_I} {S : Type u_S} {T : Type u_T} [Fintype C] [Fintype I] [Fintype S] [Fintype T]
    (νs νt : Measure Bool) [IsProbabilityMeasure νs] [IsProbabilityMeasure νt]
    (hfalse : νs {false} = 1 / 2) (htrue : νs {true} = 1 / 2)
    (center : C → S) (fresh : I → S)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → Bool)
    (addr : (S → Bool) → I → T) (haddr : ∀ a, Function.Injective (addr a))
    (p : ℝ) (hp : p ≤ 1) (hterminal : νt {false} = ENNReal.ofReal (1 - p)) :
    ((Measure.pi (fun _ : S => νs)).prod (Measure.pi (fun _ : T => νt)))
      {z : (S → Bool) × (T → Bool) |
        (∀ c, z.1 (center c) = value c) ∧
        ∀ i, z.1 (fresh i) = true → z.2 (addr z.1 i) = false} =
      (∏ c, νs {value c}) * (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by sorry
