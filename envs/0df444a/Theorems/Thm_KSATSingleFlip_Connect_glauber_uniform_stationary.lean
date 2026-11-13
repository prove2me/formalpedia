-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_glauber_uniform_stationary
-- name    : KSATSingleFlip.Connect.glauber_uniform_stationary
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:27:36.604443+00:00
-- url     : https://prove2.me/theorems/44537a57-6aa0-4ba4-8835-22035814d6de
-- title:
--   Uniform solutions are stationary for Glauber dynamics
-- statement:
--   Let $\Phi$ be a finite Boolean formula on $n>0$ variables. If $X_0$ is uniform over the satisfying assignments and each Glauber step uses an independent uniform variable and fair bit, then $X_t$ has the same uniform law for every fixed $t\ge0$. Equivalently, for every real test function $f$,
--
--   $$\mathbb E[f(X_t)]=\mathbb E[f(X_0)].$$
--
--   When the solution set is empty, both finite-uniform expectations use the formalization's zero convention. This is the fixed-formula stationarity ingredient used in Lemma 7.8 and the proof of Lemma 7.4; it does not assert the planted-law or Poisson-thinning transport.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf, Lemma 7.8 and proof of Lemma 7.4, printed pp. 57 and 65.

import Definitions.Def_KSATSingleFlip_Connect_Glauber

namespace KSATSingleFlip.Connect

/-- A uniform satisfying assignment remains uniform after any number of Glauber steps. -/
theorem glauber_uniform_stationary {n : ℕ} (hn : 0 < n)
    (Φ : GFormula (Fin n)) (f : (Fin n → Bool) → ℝ) (t : ℕ) :
    uexp (fun x : ↥(sols Φ) => uexp (fun s : Fin t → Fin n × Bool =>
      f (glauberState Φ x.1 s))) = uexp (fun x : ↥(sols Φ) => f x.1) := by sorry

end KSATSingleFlip.Connect
