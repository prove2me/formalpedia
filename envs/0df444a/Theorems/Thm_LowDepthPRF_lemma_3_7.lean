-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_3_7
-- name    : LowDepthPRF.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:44.937188+00:00
-- url     : https://prove2.me/theorems/ac650e7a-f8cb-44e9-8d26-8ed8e853caa4
-- title:
--   Lemma 3.7 — collision probability of a 2-wise independent hashing
-- statement:
--   Let $H=\{H_k:X\to Y,\ k\in K\}$ be a 2-wise independent hashing with $K$, $Y$ finite. For any distinct $x^{(1)},\dots,x^{(q)}\in X$,
--
--   $$\Pr_{k\leftarrow K}\bigl[H_k(x^{(1)}),\dots,H_k(x^{(q)})\ \text{not all distinct}\bigr]\le\frac{q^2}{2}\cdot\frac1{|Y|}.$$
--
--   It bounds the probability that the hash of Construction 4.3 fails to separate the adversary's queries.
--
--   Differences from the source:
--   - reading: 2-wise independent hashing = (2, ∞, 0)-strong pseudorandom (Def 3.6) → outputs on any ≤ 2 distinct inputs independent and uniform (NWiseIndep H 2); reason: the paper's own 'Equivalently' sentence; with the strict 'advantage less than ε' of Def 3.2, ε = 0 is unsatisfiable
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 3.7, p.12 (pdf 14)

import Mathlib
import Definitions.Def_LowDepthPRF_Pseudorandom

namespace LowDepthPRF

/-- **Lemma 3.7 (Collision Probability)** (Ding, Jain, Komargodski, arXiv:2608.25213, sha256
89a55849…, p.12). Let `H = {H_k : X → Y, k ∈ K}` be a 2-wise independent hashing. For any
distinct `x^{(1)}, …, x^{(q)} ∈ X`,
`Pr_{k ← K}[H_k(x^{(1)}), …, H_k(x^{(q)}) not all distinct] ≤ q²/2 · 1/|Y|`.

**Formalization Note.** 2-wise independence is `NWiseIndep H 2` (Definition 3.6 read through its
"Equivalently" sentence); "not all distinct" is non-injectivity of `i ↦ H_k(x^{(i)})`. `X`, `Y`
are arbitrary types, `K` and `Y` finite. -/
theorem lemma_3_7 {K X Y : Type} [Fintype K] [Fintype Y] (H : K → X → Y) (hH : NWiseIndep H 2)
    (q : ℕ) (x : Fin q → X) (hx : Function.Injective x) :
    uprob (fun k : K => ¬ Function.Injective (fun i => H k (x i))) ≤
      (q : ℝ) ^ 2 / 2 * (1 / (Fintype.card Y : ℝ)) := by sorry

end LowDepthPRF
