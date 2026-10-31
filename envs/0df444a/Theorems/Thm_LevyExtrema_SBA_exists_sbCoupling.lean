-- Prove2me | Theorems.Thm_LevyExtrema_SBA_exists_sbCoupling
-- name    : LevyExtrema.SBA.exists_sbCoupling
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:09.695245+00:00
-- url     : https://prove2.me/theorems/75349e65-a5b4-4e67-b8f5-2fc8a82b66e7
-- title:
--   §4.1, (4.1)–(4.2) — the stick-breaking coupling $(X,\ell,Y)$ exists on an extension of the probability space
-- statement:
--   Let $X$ be a Lévy process with generating triplet $(\sigma^2,\nu,b)$ on $(\Omega,\mathcal F,\mathbb P)$ that is not compound Poisson with drift, and let $T>0$. Then there are a probability space $(\Omega',\mathcal F',\mathbb P')$ with a measurable map $\pi:\Omega'\to\Omega$ such that $\mathbb P'\circ\pi^{-1}=\mathbb P$ (an extension of the original space), a Lévy process $Y$ and a sequence $(V_n)$ on $\Omega'$ such that $(X\circ\pi,\ell,Y)$ is a stick-breaking coupling on $[0,T]$:
--
--   1. $Y$ has the same generating triplet as $X$;
--   2. $(V_n)$ is i.i.d. $\mathrm U(0,1)$ and $\ell$ is the stick-breaking process it drives;
--   3. $Y$ is independent of $(V_n)$;
--   4. almost surely $(X_T,\overline X_T,\tau_T)=\sum_{k\ge1}\big(Y_{L_{k-1}}-Y_{L_k},(Y_{L_{k-1}}-Y_{L_k})^+,\ell_k\mathbb 1_{\{Y_{L_{k-1}}-Y_{L_k}>0\}}\big)$.
--
--   The paper obtains it from the law of the faces of the concave majorant of $X$ in size-biased order [PUB12, Thm 1] and a transfer theorem [Kal02, Thm 6.10]. The statement shows that the coupling hypothesis of Theorems 1 and 2 is never vacuous.
--
--   Differences from the source:
--   - encoding: a random element Y in D[0,T] and sticks ℓ_n = d_n − g_n on an extended space → a Lévy process Y on [0,∞) and a U(0,1)-iid V on Ω' with P' ∘ π⁻¹ = P, and the sticks ℓ_{k+1} = V_k L_k; reason: V_n = ℓ_n / L_{n−1} recovers the uniform weights of the sticks, and Y on [0,T] can be continued after T by an independent copy without changing (1.1); same content
--   - encoding: X is not compound Poisson with drift → ¬ IsCPPWithDrift Tr, i.e. ¬(σ = 0 ∧ ν(ℝ) < ∞); reason: a Lévy process is compound Poisson with drift exactly when σ = 0 and ν is finite; same instances
--   - encoding: Lévy process X (paths in D[0,T], X_0 = 0) → IsLevyWith P X Tr: every path càdlàg and X_0 = 0 for every ω; reason: the paper's convention that paths lie in D[0,T] (p.18); a Lévy process has a càdlàg modification with X_0 = 0
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, §4.1, (4.1)–(4.2), pp. 17–18; p. 2 ("The coupling (X, ℓ, Y) satisfying the almost sure equality in (1.1) is constructed in Subsection 4.1")

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_IsCPPWithDrift
import Definitions.Def_LevyExtrema_SBA_IsSBCoupling

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **§4.1, (4.1)–(4.2): the coupling (X, ℓ, Y) exists.**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, §4.1, pp. 17–18: "By possibly
extending the original probability space, [Kal02, Thm 6.10] asserts the existence of a random
element Y in D[0, T] such that (4.2) … Thus, this coupling between (ℓ, Y) and X is the desired one,
as (4.1) holds a.s." (p. 2: "The coupling (X, ℓ, Y) satisfying the almost sure equality in (1.1)
is constructed in Subsection 4.1 below.")

For a Lévy process `X` with triplet `Tr` that is not compound Poisson with drift and a horizon
`T > 0`, there is an extension `(Ω', P')` of the probability space (a measurable `π : Ω' → Ω`
with `P' ∘ π⁻¹ = P`), a Lévy process `Y` and a sequence `V` on it such that `(X ∘ π, V, Y)` is a
stick-breaking coupling (`IsSBCoupling`): `Y` has the triplet of `X`, `V` is U(0,1)-iid, `Y` is
independent of `V`, and (1.1) holds almost surely.

**Formalization Note.** This is the non-vacuity of the hypothesis `IsSBCoupling` used by
Theorems 1 and 2. `Ω'` lives in the universe of `Ω`. -/
theorem exists_sbCoupling {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (Tr : Triplet) (hX : IsLevyWith P X Tr)
    (hcpp : ¬ IsCPPWithDrift Tr) (T : ℝ≥0) (hT : 0 < T) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
      (Y : ℝ≥0 → Ω' → ℝ) (V : ℕ → Ω' → ℝ),
      IsProbabilityMeasure P' ∧ Measurable π ∧ P'.map π = P ∧
      IsSBCoupling P' (fun t ω' => X t (π ω')) Y V Tr T := by sorry

end LevyExtrema.SBA
