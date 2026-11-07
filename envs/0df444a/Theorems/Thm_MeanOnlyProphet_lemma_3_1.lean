-- Prove2me | Theorems.Thm_MeanOnlyProphet_lemma_3_1
-- name    : MeanOnlyProphet.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:23:07.431681+00:00
-- url     : https://prove2.me/theorems/a813ab20-10bc-476f-b21f-b14c5ca6ada4
-- title:
--   Lemma 3.1 — $0\le k(t)\le S(t)\le 1$
-- statement:
--   Let $q$ be a real rate that is nonnegative and nondecreasing on $[0,1]$, and let $S(t)=\exp(-\int_0^tq)$, $A(t)=\int_t^1S$ and $k(t)=S(t)-q(t)A(t)-A(0)e^{-q(t)}$. Then for every $t\in[0,1]$,
--   $$
--   0\le k(t)\le S(t)\le 1 .
--   $$
--   It is the basic property of $k$ used in the $n\to\infty$ analysis and in the Lipschitz estimate for $L(b,q)$.
--
--   Differences from the source:
--   - encoding: t unrestricted (the time horizon [0,1]) → t ∈ [0,1]; reason: S, A and k are defined on the horizon [0,1]
--   - encoding: nonnegative nondecreasing q → q ≥ 0 and MonotoneOn q on [0,1]; reason: the functionals read q only on [0,1]
--   - encoding: a real rate q → the extended rate toRate q (t ↦ ENNReal.ofReal (q t)) fed to the ℝ≥0∞-valued functionals; reason: q ≥ 0 on [0,1], so the values are unchanged; one set of definitions serves real and extended rates
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Lemma 3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Tinf

namespace MeanOnlyProphet

/-- **Lemma 3.1.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…),
Lemma 3.1, p.7 (PDF p.8): "Every nonnegative nondecreasing q satisfies 0 ≤ k(t) ≤ S(t) ≤ 1."

For every real rate `q` that is nonnegative and nondecreasing on `[0,1]` and every `t ∈ [0,1]`,
`0 ≤ k(t) ≤ S(t) ≤ 1` with `S(t) = exp(−∫_0^t q)`, `A(t) = ∫_t^1 S` and `k(t) = S(t) − q(t)A(t) − A(0)e^{−q(t)}`.

**Formalization Note.** The rate is real-valued as printed and enters the extended-rate functionals
as `toRate q`. -/
theorem lemma_3_1 (q : ℝ → ℝ) (hq0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q t)
    (hqm : MonotoneOn q (Set.Icc 0 1)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ kfun (toRate q) t ∧ kfun (toRate q) t ≤ survS (toRate q) t ∧ survS (toRate q) t ≤ 1 := by sorry

end MeanOnlyProphet
