-- Prove2me | Theorems.Thm_OAI_HenonLaneEmden_SpatialComponents_IsSolution_pressure_comparison
-- name    : OAI.HenonLaneEmden.SpatialComponents.IsSolution_pressure_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:38:58.582613+00:00
-- url     : https://prove2.me/theorems/f7cf4f98-419b-49e6-a966-ad02f42af4c4
-- title:
--   Directional pressure comparison for the Hénon–Lane–Emden system: weighted source layers along one direction compared through their endpoints (OpenAI Hénon–Lane–Emden theorem)
-- statement:
--   `Space n` and `IsSolution` are the definitions of the published bundle `Def_HenonEmden` ($\mathbb R^n$, and positive solutions of $-\Delta u = |x|^A v^p$, $-\Delta v = |x|^B u^q$ off the origin, continuous at it). The other definitions are from the definitions bundle `OAIQWHLE000`, following Section 5 of the paper. For a unit vector $e$, with $f$ = `source u q B` $= |x|^B u^q$, the cap weight $h_e$ = `weight volume κ e`, and the component weight $\chi_f$ = `lineWeight volume f κ δ` of the source layers $\{f > t\}$ along lines parallel to $e$ (see the published statement `OAI.HenonLaneEmden.IsSolution.angular_loss_bound` for both), the following are integrals in $[0, \infty]$ over the layer measure $dx\,dt$ on $\{0 < t < f(x)\}$ (`layerMeasure`) or over the interaction measure $d\pi = f(x)g(y)K(x-y)\,dx\,dy$ (`interaction`, $K$ the Newton kernel):
--   - `positionIntegral u f κ δ e` $= \int\!\!\int \chi_f(e,x,t)\,u(x)$;
--   - `endpointIntegral u f κ δ e` $= \int\!\!\int \chi_f(e,x,t)\,u_I$, where $u_I$ (`endpointAverage`) is the average of $u$ at the two endpoints of the layer component $I$ through $x$;
--   - `capPressureIntegral f g κ e` $= \int (n-2)\,h_e(x)\,D_e(x,y)\,d\pi$, with $D_e$ = `directionalFactor e` $= \frac{(e\cdot(x-y))^2}{|x-y|^2}$;
--   - `pairMismatchIntegral f g κ δ e` $= \int\!\!\int |\chi_f(e,x,t) - \chi_g(e,y,t')|\,K(x-y)$ over the product of the two layer measures.
--
--   **Statement.** Let $n \ge 3$, $p, q > 0$, $A, B \in \mathbb R$, $0 < \kappa \le 1$, $\delta \ge 0$, and let $e$ be a unit vector. For every solution $(u, v)$, with $f$ = `source u q B` and $g$ = `source v p A`,
--   $$\mathrm{pos}_u + \mathrm{pos}_v \;\le\; (\mathrm{end}_u + \mathrm{end}_v) + \mathrm{cap}_e + \mathrm{mis}_e,$$
--   where $\mathrm{pos}_u$ = `positionIntegral u f κ δ e`, $\mathrm{pos}_v$ = `positionIntegral v g κ δ e`, $\mathrm{end}_u$, $\mathrm{end}_v$ are the corresponding `endpointIntegral`s, $\mathrm{cap}_e$ = `capPressureIntegral f g κ e` and $\mathrm{mis}_e$ = `pairMismatchIntegral f g κ δ e`.
--
--   This is the summed and integrated form of (5.11) in Section 5.3 of the paper, obtained from the weighted interval comparison (Lemma 4.1) on pairs of parallel lines and the potential identities.
--
--   Lean: `OAI.HenonLaneEmden.SpatialComponents.IsSolution_pressure_comparison`, OpenAI's theorem of that name (in `lean/OAI/Analysis/HenonEmden/PDEPressure.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The Subcritical Hénon–Lane–Emden Conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 370; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf, Section 5.3, from Lemma 4.1 and (5.11); Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HenonEmden/PDEPressure.lean (declaration OAI.HenonLaneEmden.SpatialComponents.IsSolution_pressure_comparison)

import Mathlib
import Definitions.Def_HenonEmden
import Definitions.Def_OAIQWHLE000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PDEPressure

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open LayerTonelli

namespace SpatialComponents
open Cutoff AdaptiveCap LayerPressure

lemma IsSolution_pressure_comparison {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    positionIntegral u (source u q B) κ δ e+positionIntegral v (source v p A) κ δ e ≤
      (endpointIntegral u (source u q B) κ δ e+endpointIntegral v (source v p A) κ δ e)+
      capPressureIntegral (source u q B) (source v p A) κ e+
      pairMismatchIntegral (source u q B) (source v p A) κ δ e := by
  sorry

end SpatialComponents
end HenonLaneEmden
end
end PDEPressure

end OAI
end
