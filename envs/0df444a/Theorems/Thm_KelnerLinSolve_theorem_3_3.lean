-- Prove2me | Theorems.Thm_KelnerLinSolve_theorem_3_3
-- name    : KelnerLinSolve.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:39.229755+00:00
-- url     : https://prove2.me/theorems/29c88990-1016-496d-a852-5e15936c0b36
-- title:
--   Theorem 3.3 — SolvePerturbed returns $(I+RA)^{-1}b$ in $\tilde O((mn+n^2)s)$ bit operations and $\tilde O((m+n^2)s)$ bits
-- statement:
--   Let $A\in\mathbb Z^{n\times n}$ have $m$ nonzero entries, $b\in\mathbb Z^n$, $T_A = \max\{1,\max_{i,j}|A_{ij}|,\max_i|b_i|\}$, and $R = 2^s\ge2nT_A$ with $s\ge1$ an integer. There are one multitape machine and constants $C>0$, $K$ such that on every such input (given as $n$, $s$, $m$, the nonzero entries with their indices in any order, and $b$) the machine halts with the reduced coordinates of
--
--   $$
--   z = (I+RA)^{-1}b ,
--   $$
--
--   within $C(mn+n^2)s\cdot\mathrm{lg}(2+n+s)^K$ steps, using storage $C(m+n^2)s\cdot\mathrm{lg}(2+n+s)^K$, and every reduced numerator and denominator of $z$ has at most $Cns$ bits. No nonsingularity assumption on $A$ is made; singular $A$, for example $A=0$, is covered.
--
--   This is the exact integer core called by the floating-point solver at every precision trial.
--
--   Differences from the source:
--   - reading: a deterministic algorithm, bit operations (no machine model named) → one deterministic multitape Turing machine `IntMul.MultitapeTM`, chosen before the input, steps counted; reason: the paper names no model; a log-cost RAM simulates a multitape machine with polylog overhead, so this is the stronger reading (paper.md decision 2)
--   - reading: bits of storage → `SpaceWithin`: no head (input tape included) passes cell C(m+n²)s·polylog; reason: the model has no space notion; with fixed tapes this is the cell count up to a constant
--   - reading: Õ(·) and O(·) → C·(·)·lg(2+n+s)^K with one C, K for all inputs, no threshold on n; O(·) as C·(·); reason: §1.1's Õ suppresses polylog factors in dimension and bit length
--   - encoding: A as a list of nonzero entries, R = 2^s → the input word n#s#m#(i#j#a)*#b, indices 0-based, any order; s in place of R; reason: same data; R = 2^s is determined by s
--   - encoding: n ≥ 1 (implicit) → hypothesis 1 ≤ n; reason: excludes the empty system, where no machine meets a zero bound
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Theorem 3.3, p.10

import Mathlib
import Definitions.Def_IntMul_MultitapeWords
import Definitions.Def_KelnerLinSolve_encInt
import Definitions.Def_KelnerLinSolve_IntInstance
import Definitions.Def_KelnerLinSolve_SpaceWithin

namespace KelnerLinSolve

/-- **Theorem 3.3**, Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027
submission (sha256 d1af55cb…), p.10. "Let `A ∈ ℤ^{n×n}` have `m` nonzero entries, let `b ∈ ℤⁿ`, and let
`T_A = max{1, max_{i,j} |A_{ij}|, maxᵢ |bᵢ|}`. For `R = 2^s ≥ 2nT_A`, with integer `s ≥ 1`,
`SolvePerturbed(A, b, R)` returns `(I + RA)⁻¹b` and can be implemented to use `Õ((mn + n²)s)` bit
operations and `Õ((m + n²)s)` bits of storage. Each reduced output numerator and denominator has
`O(ns)` bits. No nonsingularity assumption on `A` is required."

One multitape machine, one `C` and one `K` serve every instance: on the input word of `(A, b, s)` it
halts with the reduced coordinates of `(I + RA)⁻¹b`, within `C (mn + n²) s lg(2 + n + s)^K` steps
and `C (m + n²) s lg(2 + n + s)^K` cells; each reduced numerator and denominator has at most `C n s`
bits.

**Formalization Note.** The input word `IntInstance.encode` lists `n`, `s`, `m`, the nonzero entries
of `A` with their `0`-based indices in any order, and `b`; the output is `a₁ # d₁ # ⋯ # aₙ # dₙ`
(`encRatVec`). There is no hypothesis on `det A`: singular `A` (for instance `A = 0`) is covered.
`1 ≤ n` excludes the empty system. -/
theorem theorem_3_3 :
    ∃ (Mc : IntMul.MultitapeTM) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ I : IntInstance, I.WellFormed → 1 ≤ I.n → 1 ≤ I.s → 2 * I.n * heightTA I.A I.rhs ≤ 2 ^ I.s →
        ∃ t : ℕ, Mc.HaltsWithOutputW I.encode t (encRatVec I.perturbedSolution) ∧
          (t : ℝ) ≤ C * (((I.m * I.n + I.n ^ 2) * I.s : ℕ) : ℝ) * polylog K (2 + I.n + I.s) ∧
          SpaceWithin Mc I.encode t (C * (((I.m + I.n ^ 2) * I.s : ℕ) : ℝ) * polylog K (2 + I.n + I.s)) ∧
          ∀ i, (bitsInt (I.perturbedSolution i).num : ℝ) ≤ C * (I.n * I.s) ∧
            (bitsInt ((I.perturbedSolution i).den : ℤ) : ℝ) ≤ C * (I.n * I.s) := by sorry

end KelnerLinSolve
