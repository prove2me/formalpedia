-- Prove2me | Theorems.Thm_LawLocalComp_lemma_4_2
-- name    : LawLocalComp.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:14:37.086746+00:00
-- url     : https://prove2.me/theorems/76674b8c-b2ff-432a-a04f-cb106032a5ed
-- title:
--   Lemma 4.2 (Shifted moment cells)
-- statement:
--   There is a family of law maps $\Phi_{q,\theta}$, computable in time polynomial in the input bits, $1/\theta$ and $\log q$, such that for $q\ge2$, rational $0<\theta\le1$ and every rational law $X$ of mean $\mu$, $Y=\Phi_{q,\theta}(X)$ is a rational conditional-mean replacement with
--   $$C_X(t)-C_Y(t)\le\theta\,\mathbb E[Y\mathbf 1\{Y>t\}]+\frac{\theta\mu}{q}\qquad(t\ge0)$$
--   and at most
--   $$1+\Big\lceil\frac{\ln(q+1)}{\ln(1+\theta)}\Big\rceil\tag{11}$$
--   atoms. With Lemma 2.3 it gives the rank upper of Theorem 1.1.
--
--   **Formalization Note** The machine reads $q,\theta$ in binary and a unary pad of length $\lceil1/\theta\rceil$.
--
--   Differences from the source:
--   - reading: bit cost polynomial in input, 1/θ, log q → PolyLawMap: one polynomial-time machine with q and θ in binary and a unary pad of length ⌈1/θ⌉₊; reason: the literal reading
--   - reading: 0 < θ ≤ 1 → rational 0 < θ ≤ 1; reason: θ is a machine input, and the paper's parameters are rational unless stated (§1, p.2)
--   - reading: certificate C_X − C_Y with no stated range of t → for t ≥ 0; reason: the range of (6), where the lemma is used
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 4.2, (11), p.7

import Mathlib
import Definitions.Def_LawLocalComp_PolyLawMap
import Definitions.Def_LawLocalComp_IsRatLaw
import Definitions.Def_LawLocalComp_IsCondMean
import Definitions.Def_LawLocalComp_call
import Definitions.Def_LawLocalComp_upperMoment
import Definitions.Def_LawLocalComp_mean

namespace LawLocalComp

/-- **Lemma 4.2 (Shifted moment cells).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 4.2, (11), p.7.

There is one polynomial-time family of maps `Φ(q, θ)` such that for `q ≥ 2`, rational `0 < θ ≤ 1` and
every rational law `X` of mean `µ`, `Y = Φ(q, θ)(X)` is a rational conditional-mean replacement with
`C_X(t) − C_Y(t) ≤ θE[Y 1{Y > t}] + θµ/q` for `t ≥ 0` and at most `1 + ⌈ln(q + 1)/ln(1 + θ)⌉` atoms.

**Formalization Note.** "Bit cost … polynomial in input, 1/θ, log q" is `PolyLawMap` with `q, θ` in
binary and a unary pad of length `⌈1/θ⌉`. The certificate is stated for `t ≥ 0`, as in (6). -/
theorem lemma_4_2 : ∃ Φ : ℕ × ℚ → Law → Law,
    PolyLawMap (fun p => [(p.1 : ℚ), p.2]) (fun p => ⌈1 / p.2⌉₊) (fun _ => True) Φ ∧
    ∀ q : ℕ, 2 ≤ q → ∀ θ : ℚ, 0 < θ → θ ≤ 1 → ∀ X : Law, IsRatLaw X →
      IsRatLaw (Φ (q, θ) X) ∧ IsCondMean X (Φ (q, θ) X) ∧
      (∀ t : ℝ, 0 ≤ t → call X t - call (Φ (q, θ) X) t ≤
        θ * upperMoment (Φ (q, θ) X) t + θ * mean X / q) ∧
      ((Φ (q, θ) X).w.support.card : ℝ) ≤ 1 + ⌈Real.log (q + 1) / Real.log (1 + θ)⌉₊ := by sorry

end LawLocalComp
