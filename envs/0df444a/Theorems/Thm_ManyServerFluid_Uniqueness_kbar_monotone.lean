-- Prove2me | Theorems.Thm_ManyServerFluid_Uniqueness_kbar_monotone
-- name    : ManyServerFluid.Uniqueness.kbar_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:00.667357+00:00
-- url     : https://prove2.me/theorems/290c6368-a647-4203-b682-62180ac196a8
-- title:
--   Proof of Corollary 4.4, p. 52 — K̄ of a fluid solution is nondecreasing
-- statement:
--   Let $(\bar X, \bar\nu)$ solve the fluid equations associated with $(\bar E, \bar X(0), \bar\nu_0) \in \mathcal S_0$, and let $\bar K(t) = \langle\mathbf 1,\bar\nu_t\rangle - \langle\mathbf 1,\bar\nu_0\rangle + \int_0^t\langle h,\bar\nu_s\rangle ds$ (3.8). Then $\bar K$ is nondecreasing on $[0,\infty)$:
--   $$0 \le s \le t \implies \bar K(s) \le \bar K(t).$$
--
--   This is what one expects from $\bar K$ as the limiting fraction of cumulative entries into service. It makes $d\bar K$ a genuine nonnegative measure, so that the entry term $\int_{[0,t]}\varphi(0,s)\,d\bar K(s)$ of (3.5) is an ordinary Lebesgue–Stieltjes integral.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 52, first claim in the proof of Corollary 4.4

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ManyServerFluid.Uniqueness

/-- Proof of Corollary 4.4, p. 52: if (X̄, ν̄) solves the fluid equations associated with
(Ē, X̄(0), ν̄_0) ∈ S_0, then K̄ of (3.8) is nondecreasing on [0, ∞). -/
theorem kbar_monotone (S : ServiceLaw) (E : ℝ → ℝ) (X0 : ℝ) (ν0 : FiniteMeasure ℝ)
    (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ) (h0 : S.InS0 E X0 ν0)
    (hsol : S.IsFluidSolution E X0 ν0 X ν) :
    MonotoneOn (S.Kbar ν) (Ici 0) := by sorry

end ManyServerFluid.Uniqueness
