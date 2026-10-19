-- Prove2me | Theorems.Thm_OAI_HenonLaneEmden_IsSolution_angular_loss_bound
-- name    : OAI.HenonLaneEmden.IsSolution.angular_loss_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:38:46.605703+00:00
-- url     : https://prove2.me/theorems/27cdab77-3f50-409a-a658-5b3cedf81c9a
-- title:
--   Averaged layer loss for the Hénon–Lane–Emden system: the direction-averaged loss of the source-layer weights is a small multiple of the energy plus a constant (OpenAI Hénon–Lane–Emden theorem)
-- statement:
--   `Space n` and `IsSolution` are the definitions of the published bundle `Def_HenonEmden` ($\mathbb R^n$, and positive solutions of $-\Delta u = |x|^A v^p$, $-\Delta v = |x|^B u^q$ off the origin, continuous at it). The other definitions are from the definitions bundle `OAIQWHLE000`, following Section 5 of the paper:
--   - `source u q B` is $f = |x|^B u^q$; `eta n` is the cutoff $\eta$; `weightedEnergy χ u q B` is $\int \chi f u$;
--   - for a unit vector $e$, `weight volume κ e` is the cap weight $h_e(x)$ of (5.2): $w(x) = -x\cdot\nabla\eta(x)$ times a normalized bump in the angle between $e$ and $x/|x|$, of angular radius $\kappa\, d(x)$ with $d(x) = \min\{1, (2-|x|)_+\}$;
--   - `layerMeasure volume f` is Lebesgue measure $dx\,dt$ on the subgraph $\{(x, t) : 0 < t < f(x)\}$, and `lineWeight volume f κ δ (e, (x, t))` is the component weight $\chi_f(e, x, t)$ of (5.7): the infimum of $h_e$ over the component $I$ of $\{f > t\}$ on the line $x + \mathbb R e$ through $x$, if $I$ is bounded with $|I| \le 2\delta \inf_I d$, and $0$ otherwise;
--   - `lossIntegral u f κ δ e` is the loss $L_f(e) = \int\!\!\int (h_e(x) - \chi_f(e, x, t))\,u(x)\,dt\,dx$ over the layer measure, in $[0, \infty]$;
--   - `lossCoefficient`, `sourceBallConstant`, `lowLevelConstant` and `uniformMassConstant` are explicit constants depending only on $n, p, q, A, B, \kappa, \delta, P$.
--
--   **Statement.** Let $n \ge 2$, $p, q > 0$, $A, B \in \mathbb R$, $0 < \kappa \le 1$, $0 < \delta \le 1/2$ and $P > 0$. For every solution $(u, v)$, with $f$ = `source u q B`,
--   $$\int_{\mathbb S^{n-1}} L_f(e)\, d\sigma(e) \;\le\; \lambda\, E_f + c_0\, P\, \max(M, 0),$$
--   where $\sigma$ is the surface measure (`volume.toSphere`), $E_f$ = `weightedEnergy (eta n) u q B`, $\lambda$ = `lossCoefficient volume κ δ (sourceBallConstant n p q A B) P`, $c_0$ = `lowLevelConstant n` and $M$ = `uniformMassConstant n p q A B`.
--
--   This is the $f$-half of Lemma 5.2 of the paper (averaged layer loss); the coefficient $\lambda$ is of the form $C_\kappa\delta + C_{\kappa,\delta}P^{-1}$, as in (5.8).
--
--   Lean: `OAI.HenonLaneEmden.IsSolution.angular_loss_bound`, OpenAI's theorem of that name (in `lean/OAI/Analysis/HenonEmden/AngularLoss.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The Subcritical Hénon–Lane–Emden Conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 370; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf, Lemma 5.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HenonEmden/AngularLoss.lean (declaration OAI.HenonLaneEmden.IsSolution.angular_loss_bound)

import Mathlib
import Definitions.Def_HenonEmden
import Definitions.Def_OAIQWHLE000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section AngularLoss

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli

lemma IsSolution.angular_loss_bound {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ P : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hP : 0 < P) :
    (∫⁻ e : sphere (0:Space n) 1, lossIntegral u (source u q B) κ δ e ∂volume.toSphere) ≤
      ENNReal.ofReal (lossCoefficient (volume : Measure (Space n)) κ δ (sourceBallConstant n p q A B) P*
        weightedEnergy (eta n) u q B+
        lowLevelConstant n*P*max (uniformMassConstant n p q A B) 0) := by
  sorry

end HenonLaneEmden
end
end AngularLoss

end OAI
end
