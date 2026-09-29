-- Prove2me | Theorems.Thm_FoundationsML_Stability_svr_stability_bound
-- name    : FoundationsML.Stability.svr_stability_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-20T04:25:52.334251+00:00
-- url     : https://prove2.me/theorems/65f4f5cc-14f2-4c53-ae6b-4cd1f9b799f1
-- title:
--   Corollary 14.5 — stability-based learning bound for SVR
-- statement:
--   **Statement (Corollary 14.5, p. 340, PDF p. 357).** Assume $K(x,x)\le r^2$ for all $x\in X$
--   and that $L_\epsilon$ is bounded by $M\ge0$ for the hypotheses SVR returns. Let $h_S$ be the
--   hypothesis returned by SVR trained on an i.i.d. sample $S$ of size $m$. Then, for any
--   $\delta>0$, with probability at least $1-\delta$:
--   $$R(h_S) \le \hat R_S(h_S) + \frac{r^2}{m\lambda} +
--     \Big(\frac{2r^2}\lambda + M\Big)\sqrt{\frac{\log(1/\delta)}{2m}}.$$
--
--   This is the chapter's flagship application: a concrete, explicit stability-based
--   generalization bound for a widely used regression algorithm, obtained by plugging
--   Proposition 14.4's specific $\beta=r^2/(m\lambda)$ (from $L_\epsilon$ being $1$-Lipschitz,
--   hence $1$-admissible) into Theorem 14.2's generic bound.
--
--   **Formalization Note.** `A` is a choice of minimizer of $F_S$ for the $\epsilon$-insensitive
--   loss, for every sample $S$, matching "the hypothesis returned by SVR when trained on … $S$";
--   the intermediate steps ($L_\epsilon$ is $1$-Lipschitz, hence $1$-admissible, so Proposition
--   14.4 gives this $\beta$) are not re-derived, only the corollary's final statement is drafted.
--   A measurability hypothesis on `z ↦ L_ε(ev(A S), z)` for every `S` guards `GeneralizationError`'s
--   Bochner integral, which sits on the left of this corollary's own load-bearing inequality.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 340, Corollary 14.5 (PDF p. 357)

import Mathlib
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_IsRKHSOf
import Definitions.Def_FoundationsML_Stability_IsMinimizer
import Definitions.Def_FoundationsML_Stability_EpsilonInsensitiveLoss

open MeasureTheory

namespace FoundationsML.Stability

/-- Corollary 14.5 (stability-based learning bound for SVR; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 340, PDF p. 357). Assume
`K(x,x) ≤ r²` for all `x ∈ X` and that `L_ε` is bounded by `M ≥ 0` for the hypotheses SVR
returns. Let `h_S` be the hypothesis returned by SVR trained on an i.i.d. sample `S` of size
`m`. Then, for any `δ > 0`, with probability at least `1 − δ`,
`R(h_S) ≤ R̂_S(h_S) + r²/(mλ) + (2r²/λ + M) sqrt(log(1/δ)/(2m))`.

**Formalization Note.** `A` is a choice of minimizer of `F_S(h) = R̂_S(h) + λ‖h‖²_K` for the
ε-insensitive loss, for every sample `S` (`hmin`), matching "the hypothesis returned by SVR
when trained on … `S`"; `β = r²/(mλ)` and `M` are plugged directly into the bound of Theorem
14.2, per the book's own proof ("Plugging this expression into the bound of theorem 14.2 yields
the result") — the intermediate steps (`L_ε` is `1`-Lipschitz, hence `1`-admissible, so
Proposition 14.4 gives this `β`) are not re-derived, only the corollary's final statement is
drafted.

**Revision (2026-09-19).** Added `hAmeas : ∀ S, Measurable (Loss (EpsilonInsensitiveLoss ε)
(ev (A S)))`, for the same reason as `stability_generalization_bound`'s own `hAmeas` — this
corollary's `GeneralizationError` also sits on the left of the load-bearing inequality. Also
corrected the citation: Eq. (14.10)/Corollary 14.5 are on printed p. 340 (PDF p. 357), not
p. 339 (PDF p. 356) as originally cited (PDF p. 356 is the tail of Proposition 14.4's proof). -/
theorem svr_stability_bound
    {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace (X × ℝ)] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ) (hRKHS : IsRKHSOf K Φ ev)
    (r : ℝ) (hr : 0 ≤ r) (hK : ∀ x : X, K x x ≤ r ^ 2)
    (ε : ℝ) (M : ℝ) (hM : 0 ≤ M)
    {m : ℕ} (hm : 0 < m) (lam : ℝ) (hlam : 0 < lam)
    (A : (Fin m → X × ℝ) → H)
    (hmin : ∀ S : Fin m → X × ℝ,
      IsMinimizer (fun g : H => EmpiricalError (EpsilonInsensitiveLoss ε) S (ev g) +
        lam * ‖g‖ ^ 2) (A S))
    (hbound : ∀ S : Fin m → X × ℝ, ∀ z : X × ℝ,
      Loss (EpsilonInsensitiveLoss ε) (ev (A S)) z ≤ M)
    (hAmeas : ∀ S : Fin m → X × ℝ, Measurable (Loss (EpsilonInsensitiveLoss ε) (ev (A S))))
    (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | GeneralizationError D (EpsilonInsensitiveLoss ε) (ev (A S)) ≤
        EmpiricalError (EpsilonInsensitiveLoss ε) S (ev (A S)) +
          r ^ 2 / (m * lam) +
          (2 * r ^ 2 / lam + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Stability
