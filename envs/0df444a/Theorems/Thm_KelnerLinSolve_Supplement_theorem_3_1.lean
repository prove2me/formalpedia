-- Prove2me | Theorems.Thm_KelnerLinSolve_Supplement_theorem_3_1
-- name    : KelnerLinSolve.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:35:25.999207+00:00
-- url     : https://prove2.me/theorems/7bba1d88-5e5b-4360-8f0a-b1af50002a34
-- title:
--   Theorem 3.1 — solver for integer inputs in $\tilde O(mn\tau)$ bit operations and $\tilde O(n^2\tau)$ bits
-- statement:
--   Let $A\in\mathbb Z^{n\times n}$ be invertible with $m$ nonzero entries and spectral condition number $\kappa=\kappa_2(A)$, let $b\in\mathbb Z^n$, and let $T_A=\max\{1,\max_{i,j}|A_{ij}|,\max_i|b_i|\}$. Assume $T_A<2^{B-1}$ and that every entry has at most $B$ bits in signed binary. Let $E\ge 0$ be an integer, $\epsilon=2^{-E}$, and
--
--   $$
--   \tau=\max(B,\ \log_2\kappa,\ \log_2(1/\epsilon)).
--   $$
--
--   There are one deterministic multitape Turing machine and constants $C>0$ and $K$ such that, on every such input (given as $n$, $E$, $m$, the nonzero entries of $A$ with their indices in any order, and $b$), the machine halts with a vector $x\in\mathbb Q^n$ written as reduced fractions, where
--
--   $$
--   \|Ax-b\|_2\le\epsilon\|b\|_2 ,
--   $$
--
--   1. the number of steps is at most $C\,mn\tau\cdot\mathrm{lg}(2+n+\lceil\tau\rceil)^K$,
--   2. no head moves past cell $C\,n^2\tau\cdot\mathrm{lg}(2+n+\lceil\tau\rceil)^K$,
--   3. every reduced numerator and denominator of $x$ has at most $C\,n\tau\cdot\mathrm{lg}(2+n+\lceil\tau\rceil)^K$ bits.
--
--   The machine is not given $\kappa$ or $B$. The case $E=0$ ($\epsilon=1$) and the case $b=0$ are included.
--
--   This is the integer core of the paper: Section 4 reduces floating-point systems to it.
--
--   Differences from the source:
--   - reading: a deterministic algorithm, bit operations (no machine model named) → one deterministic multitape Turing machine `IntMul.MultitapeTM`, chosen before the input, steps counted; reason: same reading as the base mission's goal and Theorem 3.3 (paper.md decision 1); a log-cost RAM simulates a multitape machine with polylog overhead, so this is the stronger reading
--   - reading: bits of space → `SpaceWithin`: no head (input tape included) passes cell C n²τ·polylog; reason: the model has no space notion; with a fixed number of tapes this is the cell count up to a constant
--   - reading: Õ(·) → C·(·)·lg(2+n+⌈τ⌉)^K with one C > 0 and one K for all inputs, no threshold on n; reason: §1.1's Õ suppresses factors polylogarithmic in the dimension and bit length, and the proof (p.10) absorbs log(n+1) into Õ; same convention as the base mission
--   - reading: invertible A ∈ Z^{n×n} → det A ≠ 0; reason: the page solves over ℚ and uses κ = σ_max/σ_min (p.11), i.e. nonsingularity, not unimodularity
--   - encoding: input A, b, E; output x ∈ Qⁿ → the input word n#E#m#(i#j#a)*#b with 0-based indices in any order, and the output word of reduced fractions (encRatVec); reason: same data; Lean's ℚ is reduced, and the bit bound is stated for the reduced numerators and denominators
--   - encoding: at most B bits per entry → bitsInt ≤ B for every listed (nonzero) entry of A and every entry of b; reason: an unlisted zero has bitsInt 0 = 1 ≤ B, since T_A < 2^{B−1} forces B ≥ 2
--   - encoding: n ≥ 1 (implicit) → hypothesis 1 ≤ n; reason: excludes the empty system, where no machine meets a zero bound
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Theorem 3.1, p.8

import Mathlib
import Definitions.Def_IntMul_MultitapeWords
import Definitions.Def_KelnerLinSolve_encInt
import Definitions.Def_KelnerLinSolve_kappa2
import Definitions.Def_KelnerLinSolve_SpaceWithin
import Definitions.Def_KelnerLinSolve_solvePerturbedRes
import Definitions.Def_KelnerLinSolve_Supplement_IntSolveInput

open Matrix

namespace KelnerLinSolve.Supplement

/-- **Theorem 3.1 (Solver for integer inputs)**, Kelner, *Solving Linear Systems in
Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission (sha256 d1af55cb…), p.8. "Let `A ∈ ℤ^{n×n}` be
an invertible matrix with `m` nonzero entries and condition number `κ`, let `b ∈ ℤⁿ` be a vector,
and let `T_A = max{1, max_{i,j} |A_{ij}|, maxᵢ |bᵢ|}`. Assume that `T_A < 2^{B−1}` and that the
entries are given in a signed binary representation with at most `B` bits per entry. Given an
integer `E ≥ 0`, put `ε = 2^{−E}`. There is a deterministic algorithm that finds a vector `x ∈ ℚⁿ`
such that `‖Ax − b‖₂ ≤ ε‖b‖₂` using at most `Õ(mnτ)` bit operations and `Õ(n²τ)` bits of space,
where `τ = max(B, log κ, log 1/ε)`, and the output `x` is a rational vector whose coordinates have
numerators and denominators of `Õ(nτ)` bits."

One multitape machine, one `C > 0` and one `K` serve every input: on the input word of `(A, b, E)`
it halts with the reduced coordinates of some `x ∈ ℚⁿ` with `‖Ax − b‖₂ ≤ 2^{−E}‖b‖₂`, within
`C·mnτ·lg(2 + n + ⌈τ⌉)^K` steps and `C·n²τ·lg(2 + n + ⌈τ⌉)^K` cells, and every reduced numerator
and denominator of `x` has at most `C·nτ·lg(2 + n + ⌈τ⌉)^K` bits.

**Formalization Note.**
* "Deterministic algorithm", "bit operations": one deterministic multitape Turing machine
  `IntMul.MultitapeTM`, chosen before the input, steps counted; "bits of space" is `SpaceWithin`
  (no head, input tape included, passes the bound), as in the base mission.
* The input word `IntSolveInput.encode` lists `n`, `E`, `m`, the nonzero entries of `A` with their
  `0`-based indices in any order, and `b`; it contains neither `B` nor `κ`. The output word is
  `encRatVec x` (reduced numerators and denominators).
* `Õ(T)` is `C · T · lg(2 + n + ⌈τ⌉₊)^K` with one `C`, `K` for all inputs and no threshold on `n`.
* `κ = kappa2 (A cast to ℝ)`, the spectral condition number; `τ` is `IntSolveInput.tau`.
* "at most `B` bits per entry" is `bitsInt ≤ B` for every listed entry of `A` and every entry of
  `b`; an unlisted zero entry has `bitsInt 0 = 1 ≤ B` automatically, since `T_A < 2^{B−1}` forces
  `B ≥ 2`. `1 ≤ n` excludes the empty system. -/
theorem theorem_3_1 :
    ∃ (M : IntMul.MultitapeTM) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (I : IntSolveInput) (B : ℕ), I.WellFormed → 1 ≤ I.n → I.A.det ≠ 0 →
        (heightTA I.A I.rhs : ℝ) < (2 : ℝ) ^ ((B : ℤ) - 1) →
        (∀ t ∈ I.entries, bitsInt t.2.2 ≤ B) → (∀ i, bitsInt (I.rhs i) ≤ B) →
        ∃ (x : Fin I.n → ℚ) (t : ℕ),
          M.HaltsWithOutputW I.encode t (encRatVec x) ∧
          norm2 (I.Areal *ᵥ (fun i => (x i : ℝ)) - I.breal) ≤ (2 : ℝ) ^ (-(I.E : ℤ)) * norm2 I.breal ∧
          (t : ℝ) ≤ C * ((I.m * I.n : ℕ) * I.tau B) * polylog K (2 + I.n + ⌈I.tau B⌉₊) ∧
          SpaceWithin M I.encode t (C * ((I.n ^ 2 : ℕ) * I.tau B) * polylog K (2 + I.n + ⌈I.tau B⌉₊)) ∧
          ∀ i, (bitsInt (x i).num : ℝ) ≤ C * (I.n * I.tau B) * polylog K (2 + I.n + ⌈I.tau B⌉₊) ∧
            (bitsInt ((x i).den : ℤ) : ℝ) ≤ C * (I.n * I.tau B) * polylog K (2 + I.n + ⌈I.tau B⌉₊) := by sorry

end KelnerLinSolve.Supplement
