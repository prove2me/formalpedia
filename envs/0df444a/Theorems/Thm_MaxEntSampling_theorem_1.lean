-- Prove2me | Theorems.Thm_MaxEntSampling_theorem_1
-- name    : MaxEntSampling.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:49.09098+00:00
-- url     : https://prove2.me/theorems/7d2350c8-e56f-4a21-ae90-1e4418b09476
-- title:
--   Theorem 1 — LD (5) is the Lagrangian dual of MESP (3), and $z^{LD}\ge z^*$
-- statement:
--   Let $V\in\mathbb R^{d\times n}$ have rank $d$, with columns $v_i$, so that $C=V^\top V\succeq0$ has rank $d$, and let $s\in[d]$. Write $g(\Lambda)$ for the Lagrangian dual function of MESP (3), the inner maximum in (6). Then:
--
--   1. for every $\Lambda\succ0$,
--   $$
--   g(\Lambda) = \inf\Bigl\{-\log{\det}_s(\Lambda)+s\nu+\sum_{i\in[n]}\mu_i-s : \nu\ge0,\ \mu\in\mathbb R^n_+,\ \nu+\mu_i\ge v_i^\top\Lambda v_i\ \forall i\Bigr\};
--   $$
--   2. the value of LD (5) equals the Lagrangian dual value: $z^{LD}=\inf_{\Lambda\succ0}g(\Lambda)$;
--   3. $z^{LD}\ge z^*$, where $z^*$ is the MESP value (1).
--
--   Part 3 is the weak duality used in the proof of Theorem 5.
--
--   **Formalization Note** All values are extended reals with $\log0=-\infty$; minima and maxima are infima and suprema.
--
--   Differences from the source:
--   - reading: (5) is the Lagrangian dual of MESP (3) → for every Λ ≻ 0 the dual function of (3) equals the inner optimum of (5), and z^LD = inf over Λ ≻ 0 of the dual function; reason: this is what the proof establishes through (6) and its parts (i) and (ii)
--   - encoding: Λ ⪰ 0 in (5) → Λ ≻ 0 (Matrix.PosDef); reason: a singular Λ has det_s(Λ) = 0, objective +∞, and never lowers the minimum; (6) and Lemma 1 use Λ ≻ 0
--   - reading: ν, µ ∈ R^n_+ → a scalar ν ≥ 0 and µ ∈ ℝⁿ₊; reason: ν is a scalar in (5); since v_iᵀΛv_i ≥ 0 a free ν gives the same value
--   - reading: min in (5) → infimum (sInf in EReal); reason: the paper does not prove that (5) is attained, and nothing uses attainment
--   - reading: z* of MESP (3) → z* of MESP (1) with C = VᵀV; reason: (1), (2) and (3) have the same value by Observation 1 and the substitution X = Σ x_i v_i v_iᵀ; Theorem 5 states the bound for (1)–(2)
--   - encoding: extended-real objective values → EReal with log 0 = −∞; reason: Lean convention; same instances
--   - encoding: C ⪰ 0 of rank d, C = VᵀV with V ∈ ℝ^{d×n}, and s ≤ d ≤ n → V : Matrix (Fin d) (Fin n) ℝ with V.rank = d and 1 ≤ s ≤ d; reason: C enters only through its factor V; d ≤ n follows from rank V = d ≤ n, so no instance changes
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Theorem 1, p.7 (PDF p.7), proof pp.7–8

import Mathlib
import Definitions.Def_MaxEntSampling_detBot
import Definitions.Def_MaxEntSampling_zStar
import Definitions.Def_MaxEntSampling_zLD
import Definitions.Def_MaxEntSampling_dualFn

open Matrix

namespace MaxEntSampling

/-- **Theorem 1: LD (5) is the Lagrangian dual of MESP (3), and `z^LD ≥ z*`.**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Theorem 1, p.7 (PDF p.7), proof pp.7–8: "The optimization problem below is
the Lagrangian dual of MESP (3) (LD) z^LD := min_{Λ⪰0,ν,µ∈R^n_+} { − log det_s(Λ) + sν +
Σ_{i∈[n]} µi − s : ν + µi ≥ vi^⊤Λvi, ∀i ∈ [n] }, (5) and its optimal value provides an upper
bound of MESP, i.e., z^LD ≥ z∗."

Let `V ∈ ℝ^{d×n}` have rank `d` (so `C = VᵀV ⪰ 0` has rank `d`) and `s ∈ [d]`. Then:
1. for every `Λ ≻ 0`, the Lagrangian dual function of MESP (3) at `Λ` (the inner maximum of (6))
   equals the optimal value of the inner program of (5) at `Λ`,
   `inf { −log det_s(Λ) + sν + Σ_i µ_i − s : ν ≥ 0, µ ∈ ℝⁿ₊, ν + µ_i ≥ v_iᵀΛv_i ∀ i }`;
2. the optimal value of (5) equals the Lagrangian dual value (6), `inf_{Λ≻0}` of the dual
   function;
3. `z* ≤ z^LD`, with `z*` the MESP value (1).

**Formalization Note.** All values lie in `EReal` (`log 0 = −∞`); "min" and "max" are `sInf`,
`⨅` and `⨆`. `z*` is the MESP value of (1), which equals (2) and (3) by Observation 1. `Λ`
ranges over positive definite matrices, as in (6) (see the note on `zLD`). The hypothesis
`d ≤ n` of the paper follows from `rank V = d`. -/
theorem theorem_1 {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (s : ℕ) (hs1 : 1 ≤ s) (hsd : s ≤ d)
    (hrank : V.rank = d) :
    (∀ Λ : Matrix (Fin d) (Fin d) ℝ, Λ.PosDef →
      dualFn V s Λ = sInf {z : EReal | ∃ (ν : ℝ) (μ : Fin n → ℝ), 0 ≤ ν ∧ (∀ i, 0 ≤ μ i) ∧
        (∀ i, (fun a => V a i) ⬝ᵥ (Λ *ᵥ fun a => V a i) ≤ ν + μ i) ∧
        z = ((-Real.log (detBot s Λ) + s * ν + ∑ i, μ i - s : ℝ) : EReal)}) ∧
    zLD V s = (⨅ (Λ : Matrix (Fin d) (Fin d) ℝ) (_ : Λ.PosDef), dualFn V s Λ) ∧
    zStar V s ≤ zLD V s := by sorry

end MaxEntSampling
