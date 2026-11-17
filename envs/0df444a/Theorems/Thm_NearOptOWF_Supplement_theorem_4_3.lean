-- Prove2me | Theorems.Thm_NearOptOWF_Supplement_theorem_4_3
-- name    : NearOptOWF.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:12:29.01891+00:00
-- url     : https://prove2.me/theorems/9b4e5048-bee2-4de9-91dd-3483838765f9
-- title:
--   Theorem 4.3 — a perfect pre-image sampler gives $\mathsf{coNP}\subseteq\mathsf{AM}$ infinitely often
-- statement:
--   Let $m(n)$ be polynomially related to $n$. Suppose a PPT algorithm $A$ is a perfect pre-image sampler for all circuits mapping $\{0,1\}^n$ to $\{0,1\}^{m}$. Suppose that for infinitely many $n$ there are a polynomial-size circuit $f:\{0,1\}^n\to\{0,1\}^m$ and a string $y^*\in\{0,1\}^m$ such that
--
--   1. $f$ and $y^*$ can be constructed from $1^n$ by uniform polynomial-time Turing machines,
--   2. $\Pr[A(f, y^*)\ \text{outputs a string in}\ f^{-1}(y^*)]\ge 2^{-0.9m}$, and
--   3. $\deg_f(y^*)\le 2\cdot 2^{n-m}$.
--
--   Then
--   $$
--   \mathsf{coNP}\subseteq\mathsf{AM}\quad\text{infinitely often:}
--   $$
--   every language whose complement is in $\mathsf{NP}$ agrees, on all inputs of length $n$ for infinitely many $n$, with some language in $\mathsf{AM}$.
--
--   This is the warm-up of the paper: an idealized inverter, together with a single good instance per length, certifies unsatisfiability in $\mathsf{AM}$. The full proof of Theorem 4.1 replaces the perfect sampler by one obtained from an arbitrary inverter.
--
--   Differences from the source:
--   - reading: m = poly(n) → m(n) ≤ q(n) for a polynomial q and m(n) ≥ n^c for some c > 0 and all large n; reason: under the literal reading m(n) ≤ q(n) a constant m is allowed, and then the rejection sampler with f(x) = 0^m on a 2^{1−m} fraction of inputs meets every hypothesis, so the statement would assert coNP ⊆ AM i.o. unconditionally; the proof (Claim 4.5, 2^{n^δ−m+1} ≤ 2^{−0.9m}/2 for small δ) needs m ≥ n^{Ω(1)}
--   - reading: f and y* can be constructed by uniform Turing machines → one polynomial-time machine each computes the description of f = F n and y* = Y n from 1^n, for every n in the infinite set S of the bullets; reason: uniform construction means polynomial-time generation; the proof's AM protocol builds the planted circuit f_φ from φ, which needs f and y* in polynomial time, and polynomial size of f follows
--   - encoding: perfect pre-image sampler for all polynomial-size circuits {0,1}^n → {0,1}^m → for all circuits with n inputs and m(n) output wires, every n; reason: each single circuit has constant, hence polynomial, size, so the two classes coincide
--   - encoding: identically distributed outputs, conditioned on not ⊥ uniform on f^{-1}(y) → equal probabilities of every valid pre-image (rawProb); ⊥ is every other output; reason: the distribution over pre-images and ⊥ is determined by these probabilities
--   - encoding: coNP ⊆ AM infinitely often → every L with Lᶜ ∈ NP agrees infinitely often (AgreeIO) with some L′ such that L′ᶜ ∈ coAM (InCoAMPoly); reason: the base mission's reading of ⊆_{i.o.}; L′ ∈ AM iff its complement is in coAM
--   - encoding: a PPT algorithm A run on (f, y) → a base Inverter with Inverter.IsPPT (one uniform polynomial-time machine, polynomially many coins) run on the tuple (1^n, code of f, y); reason: the base mission's PPT model; the code of f already contains 1^n, so the extra input changes no instance
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.3, p.13 (PDF p.15); proof with Claims 4.4–4.5, pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_NearOptOWF_Supplement_IsPerfectPreimageSampler
import Definitions.Def_NearOptOWF_Supplement_preimSuccProb
import Definitions.Def_NearOptOWF_Supplement_deg
import Definitions.Def_NearOptOWF_Inverter_IsPPT
import Definitions.Def_NearOptOWF_InNP
import Definitions.Def_NearOptOWF_AgreeIO
import Definitions.Def_LaconicBarrier_InCoAMPoly
import Definitions.Def_LaconicBarrier_PolyTimeOn

namespace NearOptOWF.Supplement

open LaconicBarrier

/-- **Theorem 4.3** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.3, p.13 (PDF p.15)): suppose a PPT algorithm `A` is a perfect
pre-image sampler for all circuits mapping `{0,1}ⁿ` to `{0,1}^{m(n)}`, where `m = poly(n)`. Suppose that
for infinitely many `n` (the set `S`) there are a circuit `f = F n : {0,1}ⁿ → {0,1}^{m(n)}` and a string
`y* = Y n ∈ {0,1}^{m(n)}` such that

* `f` and `y*` are constructed from `1ⁿ` by uniform polynomial-time machines (so `f` has polynomial size),
* `Pr[A(f, y*) outputs a string in f⁻¹(y*)] ≥ 2^{−0.9m}`, and
* `deg_f(y*) ≤ 2 · 2^{n−m}`.

Then `coNP ⊆ AM` infinitely often: every language `L` whose complement is in NP agrees infinitely often
(base `AgreeIO`) with some language `L′ ∈ AM` (`L′ᶜ ∈ coAM`).

**Formalization Note** "`m = poly(n)`" is read as *polynomially related*: `m(n) ≤ q(n)` for a polynomial
`q` and `m(n) ≥ n^c` for some `c > 0` and all large `n`. Under the literal reading `m(n) ≤ q(n)` a constant
`m` is allowed, and then rejection sampling with the planted circuit `f(x) = 0^m` on `1/2^{m−1}` of the
inputs meets every hypothesis, so the theorem would give `coNP ⊆ AM` i.o. unconditionally; the proof
(Claim 4.5, `2^{n^δ−m+1} ≤ 2^{−0.9m}/2`) needs `m ≥ n^{Ω(1)}`. The machines constructing `f` and `y*` work
on the lengths in `S`. The success probability is over `A`'s coins only. -/
theorem theorem_4_3 (A : Inverter) (hA : A.IsPPT) (m : ℕ → ℕ)
    (hm_up : ∃ q : Polynomial ℕ, ∀ n, m n ≤ q.eval n)
    (hm_lo : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ c ≤ (m n : ℝ))
    (hPerf : IsPerfectPreimageSampler A m)
    (S : Set ℕ) (hS : S.Infinite) (F : (n : ℕ) → MCircuit n) (Y : ℕ → List Bool)
    (hF : PolyTimeOn (ι := S) (fun n => [unary n.1]) (fun n => (F n.1).code))
    (hY : PolyTimeOn (ι := S) (fun n => [unary n.1]) (fun n => Y n.1))
    (hdim : ∀ n ∈ S, (F n).outs.length = m n ∧ (Y n).length = m n)
    (hsucc : ∀ n ∈ S, (2 : ℝ) ^ (-(0.9 : ℝ) * (m n : ℝ)) ≤ preimSuccProb A (F n) (Y n))
    (hdeg : ∀ n ∈ S, (deg (F n) (Y n) : ℝ) ≤ 2 * (2 : ℝ) ^ ((n : ℝ) - (m n : ℝ))) :
    ∀ L : Set (List Bool), InNP Lᶜ →
      ∃ L' : Set (List Bool), InCoAMPoly L'ᶜ ∧ AgreeIO L L' := by sorry

end NearOptOWF.Supplement
