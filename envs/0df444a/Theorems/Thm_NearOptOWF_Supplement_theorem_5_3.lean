-- Prove2me | Theorems.Thm_NearOptOWF_Supplement_theorem_5_3
-- name    : NearOptOWF.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:15:50.081232+00:00
-- url     : https://prove2.me/theorems/30942a6f-8b8a-46a0-8c8e-a8a2a6777441
-- title:
--   Theorem 5.3 — a perfect collision sampler gives $\mathsf{NP}\subseteq\mathsf{coAM}$ infinitely often
-- statement:
--   Suppose a PPT algorithm $A$ is a perfect collision sampler for circuits mapping $\{0,1\}^n$ to $\{0,1\}^{n-1}$. Suppose that for infinitely many $n$ there are a polynomial-size circuit $f:\{0,1\}^n\to\{0,1\}^{n-1}$ and a string $y^\star\in\{0,1\}^{n-1}$ such that
--
--   1. $f$ and $y^\star$ can be constructed from $1^n$ by uniform polynomial-time Turing machines,
--   2. $\Pr[A(f)\ \text{outputs a collision on}\ y^\star]\ge 2^{-n}$, and
--   3. $\deg_f(y^\star)\le 2^{n/3}$.
--
--   Then
--   $$
--   \mathsf{NP}\subseteq\mathsf{coAM}\quad\text{infinitely often:}
--   $$
--   every language in $\mathsf{NP}$ agrees, on all inputs of length $n$ for infinitely many $n$, with some language in $\mathsf{coAM}$.
--
--   This is the collision-resistance warm-up for Theorem 5.2, the analogue of Theorem 4.3 for pairs of pre-images.
--
--   Differences from the source:
--   - reading: f and y* can be constructed by uniform Turing machines → one polynomial-time machine each computes the description of f = F n and y* = Y n from 1^n, for every n in the infinite set S of the bullets; reason: uniform construction means polynomial-time generation; the proof's AM protocol builds the planted circuit f_φ from φ, which needs f and y* in polynomial time, and polynomial size of f follows
--   - encoding: perfect collision sampler for polynomial-size circuits {0,1}^n → {0,1}^{n−1} → for all circuits with n inputs and n − 1 output wires, every n; reason: each single circuit has constant, hence polynomial, size, so the two classes coincide
--   - encoding: A(f) outputs a pair {x, x′} or ⊥; uniform over unordered pairs → an output of length 2n split into halves (x, x′); uniformity as equal sums Pr[(x,x′)] + Pr[(x′,x)] over unordered pairs; reason: a fixed injective encoding of pairs; pooling the two orders is the unordered-pair distribution
--   - encoding: NP ⊆ coAM infinitely often → every L ∈ NP agrees infinitely often (AgreeIO) with some L′ ∈ coAM (InCoAMPoly); reason: the base mission's reading of ⊆_{i.o.}; this is the negation of the base hypothesis NPNotSubsetIoCoAM
--   - encoding: a PPT algorithm A run on f → a base Inverter with Inverter.IsPPT (one uniform polynomial-time machine, polynomially many coins) run on the tuple (1^n, code of f); reason: the base mission's PPT model; the code of f already contains 1^n, so the extra input changes no instance
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §5.1 and Theorem 5.3, p.24 (PDF p.26); proof with Claims 5.4–5.5, pp.24–25

import Mathlib
import Definitions.Def_NearOptOWF_Supplement_IsPerfectCollisionSampler
import Definitions.Def_NearOptOWF_Supplement_collSuccProb
import Definitions.Def_NearOptOWF_Supplement_deg
import Definitions.Def_NearOptOWF_Inverter_IsPPT
import Definitions.Def_NearOptOWF_InNP
import Definitions.Def_NearOptOWF_AgreeIO
import Definitions.Def_LaconicBarrier_InCoAMPoly
import Definitions.Def_LaconicBarrier_PolyTimeOn

namespace NearOptOWF.Supplement

open LaconicBarrier

/-- **Theorem 5.3** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 5.3, p.24 (PDF p.26)): suppose a PPT algorithm `A` is a perfect
collision sampler for circuits mapping `{0,1}ⁿ` to `{0,1}^{n−1}`. Suppose that for infinitely many `n` (the
set `S`) there are a circuit `f = F n : {0,1}ⁿ → {0,1}^{n−1}` and a string `y* = Y n ∈ {0,1}^{n−1}` such
that

* `f` and `y*` are constructed from `1ⁿ` by uniform polynomial-time machines (so `f` has polynomial size),
* `Pr[A(f) outputs a collision on y*] ≥ 2^{−n}`, and
* `deg_f(y*) ≤ 2^{n/3}`.

Then `NP ⊆ coAM` infinitely often: every language `L ∈ NP` agrees infinitely often (base `AgreeIO`) with
some language `L′ ∈ coAM`, that is, the base hypothesis `NPNotSubsetIoCoAM` fails.

**Formalization Note** The machines constructing `f` and `y*` work on the lengths in `S`. The collision
probability is over `A`'s coins only. -/
theorem theorem_5_3 (A : Inverter) (hA : A.IsPPT) (hPerf : IsPerfectCollisionSampler A)
    (S : Set ℕ) (hS : S.Infinite) (F : (n : ℕ) → MCircuit n) (Y : ℕ → List Bool)
    (hF : PolyTimeOn (ι := S) (fun n => [unary n.1]) (fun n => (F n.1).code))
    (hY : PolyTimeOn (ι := S) (fun n => [unary n.1]) (fun n => Y n.1))
    (hdim : ∀ n ∈ S, (F n).outs.length = n - 1 ∧ (Y n).length = n - 1)
    (hsucc : ∀ n ∈ S, (2 : ℝ) ^ (-(n : ℝ)) ≤ collSuccProb A (F n) (Y n))
    (hdeg : ∀ n ∈ S, (deg (F n) (Y n) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 3)) :
    ∀ L : Set (List Bool), InNP L →
      ∃ L' : Set (List Bool), InCoAMPoly L' ∧ AgreeIO L L' := by sorry

end NearOptOWF.Supplement
