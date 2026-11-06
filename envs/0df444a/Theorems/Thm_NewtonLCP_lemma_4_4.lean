-- Prove2me | Theorems.Thm_NewtonLCP_lemma_4_4
-- name    : NewtonLCP.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:30:30.328219+00:00
-- url     : https://prove2.me/theorems/8e8d58ad-e43a-479c-8759-d1d145d6e5cd
-- title:
--   Lemma 4.4 — progress lemma in $\mathcal N^2(\beta)$
-- statement:
--   Assume $M\in\mathcal P_\star(\kappa)$. Let $\beta\in\big(0,\frac1{4(1+\kappa)}\big]$ and $\delta\in\big(0,\frac{\beta}{2\sqrt n}\big]$, let $(x,s,\mu)\in\mathcal N^2(\beta)$ and $\mu'=\mu/(1+\delta)$. Let $(\Delta x,\Delta s)$ be the Newton step (10) from $(x,s,\mu')$ and $(x',s')=(x+\Delta x,s+\Delta s)$. Then
--
--   $$(x',s',\mu')\in\mathcal N^2(\beta).$$
--
--   This gives the classical $O(\sqrt n(1+\kappa)\log(\mu^0/\mu_1))$ bound for the first branch of (54).
--
--   Differences from the source:
--   - encoding: δ ∈ (0, β/(2√n)] for n = 0 → the Lean interval (0, β/(2·√0)] = (0, 0] is empty, so the statement is vacuous at n = 0; reason: β/(2√n) is undefined at n = 0; nothing changes for n ≥ 1
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Lemma 4.4, p.13

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_NewtonStep

namespace NewtonLCP

/-- **Lemma 4.4** (progress lemma). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Lemma 4.4, p.13.

Assume `M ∈ P⋆(κ)`. For any `β ∈ (0, 1/(4(1+κ))]`, `δ ∈ (0, β/(2√n)]`, let
`(x, s, µ) ∈ N²(β)`, `µ' = µ/(1+δ)`, let `(∆x, ∆s)` be computed from solving (10) for `µ'`, and
`(x', s') = (x + ∆x, s + ∆s)`. Then `(x', s', µ') ∈ N²(β)`.

**Formalization Note.** `n = Fintype.card ι`. The Newton step is taken at `(x, s, µ')`. At
`n = 0` the interval `(0, β/(2√n)]` is `(0, 0]` in Lean and the statement is vacuous, as the
printed `β/(2√0)` is undefined. -/
theorem lemma_4_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (κ β δ : ℝ) (x s : ι → ℝ) (mu : ℝ) (hM : IsPStarK M κ)
    (hβ0 : 0 < β) (hβ : β ≤ 1 / (4 * (1 + κ)))
    (hδ0 : 0 < δ) (hδ : δ ≤ β / (2 * Real.sqrt (Fintype.card ι)))
    (hN : InN2 M q β x s mu) :
    InN2 M q β (x + newtonDx M x s (mu / (1 + δ))) (s + newtonDs M x s (mu / (1 + δ)))
      (mu / (1 + δ)) := by sorry

end NewtonLCP
