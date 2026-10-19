-- Prove2me | Theorems.Thm_OAI_HenonLaneEmden_IsSolution_integrated_directional_pressure
-- name    : OAI.HenonLaneEmden.IsSolution.integrated_directional_pressure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:38:50.071487+00:00
-- url     : https://prove2.me/theorems/2e3a004e-cad5-4de9-9263-72634be39492
-- title:
--   Direction-integrated pressure inequality for the Hénon–Lane–Emden system (OpenAI Hénon–Lane–Emden theorem)
-- statement:
--   `Space n` and `IsSolution` are the definitions of the published bundle `Def_HenonEmden` ($\mathbb R^n$, and positive solutions of $-\Delta u = |x|^A v^p$, $-\Delta v = |x|^B u^q$ off the origin, continuous at it). The other definitions are from the definitions bundle `OAIQWHLE000`, following Section 5 of the paper:
--   - `source u q B` is $f = |x|^B u^q$; `w n` is $w(x) = -x\cdot\nabla\eta(x)$ for OpenAI's cutoff $\eta$; `d` is $d(x) = \min\{1, (2-|x|)_+\}$;
--   - `weightedEnergyN χ u q B` is $\int \chi f u$ as a lower Lebesgue integral in $[0, \infty]$;
--   - for a unit vector $e$: `capPressureIntegral f g κ e` $= \int (n-2)\,h_e(x)\,D_e(x,y)\,d\pi$ and `capMismatchIntegral f g κ e` $= \int |h_e(x) - h_e(y)|\,d\pi$, with the cap weight $h_e$ = `weight volume κ e`, $D_e$ = `directionalFactor e` $= \frac{(e\cdot(x-y))^2}{|x-y|^2}$ and the interaction measure $d\pi = f(x)g(y)K(x-y)\,dx\,dy$ (`interaction`, $K$ the Newton kernel); `lossIntegral u f κ δ e` is the layer loss $L_f(e)$ (see the published statement `OAI.HenonLaneEmden.IsSolution.angular_loss_bound`);
--   - `endpointConstant q B` is the explicit constant $2\,|B/q|\,2^{|{-B/q}-1|}\,2^{|B/q|}$.
--
--   **Statement.** Let $n \ge 3$, $p, q > 0$, $A, B \in \mathbb R$, $0 < \kappa \le 1$ and $\delta \ge 0$. For every solution $(u, v)$, with $f$ = `source u q B`, $g$ = `source v p A` and $\sigma$ the surface measure on the unit sphere (`volume.toSphere`),
--   $$\frac{1}{q+1}\int w f u + \frac{1}{p+1}\int w g v \;\le\; \int_{\mathbb S^{n-1}} \mathrm{cap}_e\,d\sigma + \int_{\mathbb S^{n-1}} \mathrm{mis}_e\,d\sigma + 2\Bigl(\int_{\mathbb S^{n-1}} L_f\,d\sigma + \int_{\mathbb S^{n-1}} L_g\,d\sigma\Bigr) + c_{q,B}\,\delta\!\int d\,w f u + c_{p,A}\,\delta\!\int d\,w g v,$$
--   in $[0, \infty]$, where $\mathrm{cap}_e$ = `capPressureIntegral f g κ e`, $\mathrm{mis}_e$ = `capMismatchIntegral f g κ e`, $L_f$ = `lossIntegral u f κ δ`, $L_g$ = `lossIntegral v g κ δ`, $c_{q,B}$ = `endpointConstant q B` and $c_{p,A}$ = `endpointConstant p A`.
--
--   This is the combination of (5.12) and (5.14) in Section 5.4 of the paper, averaged over the direction $e$ (here integrated against the unnormalized surface measure), before the choice of $\kappa$, $\delta$ and $P$ in the proof of Proposition 5.1.
--
--   Lean: `OAI.HenonLaneEmden.IsSolution.integrated_directional_pressure`, OpenAI's theorem of that name (in `lean/OAI/Analysis/HenonEmden/IntegratedPressure.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The Subcritical Hénon–Lane–Emden Conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 370; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf, Section 5.4, (5.12)–(5.14) averaged over directions; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HenonEmden/IntegratedPressure.lean (declaration OAI.HenonLaneEmden.IsSolution.integrated_directional_pressure)

import Mathlib
import Definitions.Def_HenonEmden
import Definitions.Def_OAIQWHLE000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section IntegratedPressure

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli

lemma IsSolution.integrated_directional_pressure {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (1/(q+1))*weightedEnergyN (w n) u q B+
      ENNReal.ofReal (1/(p+1))*weightedEnergyN (w n) v p A ≤
      (∫⁻ e : sphere (0:Space n) 1, capPressureIntegral (source u q B) (source v p A) κ e ∂volume.toSphere)+
      (∫⁻ e : sphere (0:Space n) 1, capMismatchIntegral (source u q B) (source v p A) κ e ∂volume.toSphere)+
      2*((∫⁻ e : sphere (0:Space n) 1, lossIntegral u (source u q B) κ δ e ∂volume.toSphere)+
        (∫⁻ e : sphere (0:Space n) 1, lossIntegral v (source v p A) κ δ e ∂volume.toSphere))+
      (ENNReal.ofReal (endpointConstant q B*δ)*weightedEnergyN (fun x => d x*w n x) u q B+
      ENNReal.ofReal (endpointConstant p A*δ)*weightedEnergyN (fun x => d x*w n x) v p A) := by
  sorry

end HenonLaneEmden
end
end IntegratedPressure

end OAI
end
