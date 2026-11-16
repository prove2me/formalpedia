-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_A_4
-- name    : GeoQAC.Supplement.theorem_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:29:57.178601+00:00
-- url     : https://prove2.me/theorems/03af1996-bf24-44a9-b513-a4c40b469734
-- title:
--   Theorem A.4 — sample complexity of learning $\mathcal F_{h,w,d}$
-- statement:
--   There is an absolute constant $C_0>0$ such that the following holds. Fix a layout: a grid $[w]\times[h]$, a depth bound $d$ and the positions of the $n$ input qubits, the ancillas starting in $|0\rangle$. For all $\varepsilon,\delta\in(0,1)$ there are a sample size
--   $$
--   m\le C_0\cdot\frac{h\,2^{(4d+1)w}\log(2h)+\log(1/\delta)}{\varepsilon}
--   $$
--   and a learner $L$, mapping $m$ labeled examples to a hypothesis, such that for every $f\in\mathcal F_{h,w,d}$ (the functions computed exactly on this layout at depth at most $d$): with probability at least $1-\delta$ over $m$ independent uniform examples $(x_i,f(x_i))$, the hypothesis $\tilde f$ returned by $L$ satisfies $\Pr_x[\tilde f(x)\ne f(x)]\le\varepsilon$.
--
--   Functions computed exactly by constant-depth circuits of logarithmic width and polynomial length are thus learnable from polynomially many classical examples. The bound concerns samples, not running time.
--
--   Differences from the source:
--   - encoding: O(·) examples; probabilities over i.i.d. uniform examples → one absolute C₀ with m ≤ C₀(…)/ε; finite counts over the 2^{nm} example tuples and the 2^n inputs; reason: §2.1 makes implicit constants absolute; uniform sampling on a finite set is counting
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem A.4, p.38

import Mathlib
import Definitions.Def_GeoQAC_Supplement_InExactClass

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem A.4** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.38). Setting (p.38): "fix
the parameters `h, w, d` and the locations of the `n` input qubits and `a = wh − n` ancillas, all
known to the learner. The ancillas begin in a fixed product state, which we take to be `|0^a⟩` by
one-qubit gates. Let `F_{h,w,d}` be the Boolean functions decided exactly by circuits on this layout
with depth at most `d`. The learner receives independent classical examples `(x, f(x))`, with `x`
uniform on `{0,1}^n`, and may return a hypothesis outside `F_{h,w,d}`." Theorem: "For every
`ε, δ ∈ (0, 1)`, the class `F_{h,w,d}` can be learned from
`O((h 2^{(4d+1)w} log(2h) + log(1/δ))/ε)` uniform labeled examples. With probability at least
`1 − δ`, the returned hypothesis `f̃` satisfies `Pr_x[f̃(x) ≠ f(x)] ≤ ε`."

**Formalization Note.**
* One absolute constant `C₀`. For each layout `(w, h, inp)` and `ε, δ` there are a sample size `m`
  within the bound and a learner `L` (any function of the `m` labeled examples; no running time is
  bounded, p.39) that `(ε, δ)`-learns every `f ∈ F_{h,w,d}` (`InExactClass`, `LearnsTarget`: the
  `m` examples are i.i.d. uniform, so probabilities are finite counts).
* `log` is natural (p.9: any fixed base). -/
theorem theorem_A_4 : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (w h d n : ℕ) (inp : Fin n ↪ Pos w h) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∃ (m : ℕ) (L : (Fin m → (Fin n → Bool) × Bool) → (Fin n → Bool) → Bool),
        (m : ℝ) ≤ C₀ * ((h : ℝ) * 2 ^ ((4 * d + 1) * w) * Real.log (2 * h) +
            Real.log (1 / δ)) / ε ∧
        ∀ f : (Fin n → Bool) → Bool, InExactClass w h d inp f → LearnsTarget L f ε δ := by sorry

end GeoQAC.Supplement
