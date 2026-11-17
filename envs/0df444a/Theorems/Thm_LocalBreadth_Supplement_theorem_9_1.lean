-- Prove2me | Theorems.Thm_LocalBreadth_Supplement_theorem_9_1
-- name    : LocalBreadth.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:27:58.505571+00:00
-- url     : https://prove2.me/theorems/1c708938-788a-44ca-883a-c821a2a169e0
-- title:
--   Theorem 9.1 — failure of exact half-density for the known target $\mathbb Z^d$
-- statement:
--   Fix $d\ge2$ and the known target $K=\mathbb Z^d$. Let $h:\mathbb N_{\ge1}\to(0,\infty)$ be nondecreasing with $\sup_{n\ge1}n/h(n)=\infty$. For every causal generator satisfying the freshness condition on full enumerations of $\mathbb Z^d$, there is a full enumeration of $\mathbb Z^d$ on which
--   $$\delta_h(O,\mathbb Z^d)<\tfrac12.$$
--
--   So the loss $\varepsilon$ in Theorem 8.2 cannot be removed in general, even for the rank-zero family $\{\mathbb Z^d\}$ and even for $h\equiv1$.
--
--   Differences from the source:
--   - encoding: h : ℕ_{≥1} → (0, ∞) → h : ℕ → ℝ with positivity and monotonicity required on n ≥ 1 only; reason: δ_h evaluates h only at volumes V(R) ≥ 1, so the value h 0 is never used
--   - encoding: causal generator → GeneratorP (Fin d → ℤ): the output at time t is a function of x 0, …, x t; reason: every generator of the model is causal; outputs may be anywhere in ℤ^d (Lemma 9.2)
--   - encoding: time t = 1, 2, … with inputs x_t, outputs o_t → 0-indexed time; the output at time t is G applied to x 0, …, x t; reason: index shift only; the same runs
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §9, Theorem 9.1, p.71 (PDF p.73)

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_GeneratorP
import Definitions.Def_LocalBreadth_Supplement_deltaH

namespace LocalBreadth.Supplement

/-- Theorem 9.1 (failure of exact half-density). Kleinberg, Wei, STOC 2027 submission (manuscript
sha256 f924cbfc…), §9, p.71. Fix `d ≥ 2` and the known target `K = ℤ^d`. Let `h : ℕ_{≥1} → (0, ∞)` be
nondecreasing with `sup_{n ≥ 1} n / h(n) = ∞`. For every causal generator satisfying the freshness
condition there is a full enumeration of `ℤ^d` on which `δ_h(O, ℤ^d) < 1/2`.

**Formalization Note.** The family is `{ℤ^d}`; freshness is required on full enumerations of `ℤ^d`.
Generators are causal by construction (the output at time `t` sees the inputs up to time `t`) and may
output anywhere in `ℤ^d`. -/
theorem theorem_9_1 (d : ℕ) (hd : 2 ≤ d) (h : ℕ → ℝ) (hh : IsThreshold h)
    (hsup : ¬ BddAbove ((fun n : ℕ => (n : ℝ) / h n) '' Set.Ici 1))
    (G : GeneratorP (Fin d → ℤ)) (hG : IsFreshP {Set.univ} G) :
    ∃ x, IsFullEnumerationP (Set.univ : Set (Fin d → ℤ)) x ∧
      deltaH h (outputSetP G x) Set.univ < 1 / 2 := by sorry

end LocalBreadth.Supplement
