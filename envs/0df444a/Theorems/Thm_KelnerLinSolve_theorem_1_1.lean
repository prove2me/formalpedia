-- Prove2me | Theorems.Thm_KelnerLinSolve_theorem_1_1
-- name    : KelnerLinSolve.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:49.417194+00:00
-- url     : https://prove2.me/theorems/e24c6b47-d04d-4fc3-8ccb-ebd72365f76f
-- title:
--   Theorem 1.1 (Main) — a deterministic floating-point solver with relative residual $2^{-E}$ in $\tilde O((m+n)(B_{\mathrm{sig}}+B_{\mathrm{exp}})+mn\rho)$ bit operations
-- statement:
--   There are one deterministic multitape Turing machine and constants $C>0$, $K$ with the following property. Let $A\in\mathbb R^{n\times n}$, $n\ge1$, be nonsingular with $m$ nonzero entries and $b\in\mathbb R^n$, every entry supplied exactly as $u2^e$ with $\mathrm{bits}(u)\le B_{\mathrm{sig}}$ and $\mathrm{bits}(e)\le B_{\mathrm{exp}}$ (the matrix as a list of its nonzero entries with their indices, in any order, the right-hand side as a vector, zero entries included). Let $\varepsilon = 2^{-E}$ with an integer $E\ge1$, and
--
--   $$
--   \rho = 1+E+\lceil\log_2\kappa_2(A)\rceil+\lceil\log_2(n+1)\rceil .
--   $$
--
--   On the input word of $(A, b, E)$, which contains no condition-number bound and no $B_{\mathrm{sig}}$, $B_{\mathrm{exp}}$, the machine halts with integers $q_1,\dots,q_n,\gamma$ such that $\hat x_i = q_i2^\gamma$ satisfies
--
--   $$
--   \|A\hat x-b\|_2\le\varepsilon\|b\|_2 ,
--   $$
--
--   within $\tilde O\big((m+n)(B_{\mathrm{sig}}+B_{\mathrm{exp}})+mn\rho\big)$ steps and $\tilde O\big((m+n)(B_{\mathrm{sig}}+B_{\mathrm{exp}})+n^2\rho\big)$ cells of storage; each $q_i$ has $O(\rho)$ bits and $\gamma$ has $O(B_{\mathrm{exp}}+\log(B_{\mathrm{sig}}+\rho+1))$ bits. Here $\tilde O(X)$ means $C\cdot X\cdot\mathrm{lg}(2+n+B_{\mathrm{sig}}+B_{\mathrm{exp}}+\rho)^K$ and $O(X)$ means $C\cdot X$, with the same $C,K$ for all inputs.
--
--   For polylogarithmic encodings, polynomial conditioning and inverse-polynomial accuracy this is $\tilde O(mn)$, and $\tilde O(n^2)$ for sparse $A$.
--
--   Differences from the source:
--   - reading: a deterministic algorithm, bit operations (no machine model named) → one deterministic multitape Turing machine `IntMul.MultitapeTM`, chosen before the input, steps counted; reason: the paper names no model; a log-cost RAM simulates a multitape machine with polylog overhead, so this is the stronger reading (paper.md decision 2)
--   - reading: storage … bits → `SpaceWithin`: no head (input tape included) passes cell C·(…)·polylog; reason: the model has no space notion; with fixed tapes this is the cell count up to a constant (paper.md decision 2)
--   - reading: Õ(·) and O(·) → C·(·)·lg(2+n+B_sig+B_exp+ρ)^K with one C, K for all inputs and no threshold on n; O(·) as C·(·); reason: §1.1: Õ suppresses factors polylogarithmic in the dimension and bit length (paper.md decision 3)
--   - encoding: the matrix as a list of nonzero entries and indices, the right-hand side as encoded entries → the word `encInst` (binary and signed binary, # separators, 0-based indices, any order); reason: same data; contains no κ, B_sig, B_exp
--   - encoding: returns integers q₁, …, qₙ, γ → the output tape holds q₁#…#qₙ#γ when the machine halts; reason: same output
--   - encoding: n ≥ 1 (implicit) → hypothesis 1 ≤ n; reason: excludes the empty system, where κ₂ is meaningless and no machine meets a zero bound (paper.md decision 4)
--   - encoding: A nonsingular → det A ≠ 0; reason: same matrices
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Theorem 1.1, p.3 (§1.1 conventions, p.3)

import Mathlib
import Definitions.Def_IntMul_MultitapeWords
import Definitions.Def_KelnerLinSolve_FloatInstance
import Definitions.Def_KelnerLinSolve_kappa2
import Definitions.Def_KelnerLinSolve_SpaceWithin

open Matrix

namespace KelnerLinSolve

/-- **Theorem 1.1 (Main)**, Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC
2027 submission (sha256 d1af55cb…), p.3. "Let `A ∈ ℝ^{n×n}` be nonsingular with `m` nonzero entries,
and let `b ∈ ℝⁿ`. Suppose every entry is supplied exactly as `u2^e` with `bits(u) ≤ B_sig` and
`bits(e) ≤ B_exp`. Let `ε = 2^{−E}` for an integer `E ≥ 1`, and let
`ρ = 1 + E + ⌈log₂ κ₂(A)⌉ + ⌈log₂(n + 1)⌉`. There is a deterministic algorithm that returns integers
`q₁, …, qₙ, γ` such that `x̂ᵢ = qᵢ2^γ`, `‖Ax̂ − b‖₂ ≤ ε‖b‖₂`. Its running time and storage are,
respectively, `Õ((m + n)(B_sig + B_exp) + mnρ)` bit operations, `Õ((m + n)(B_sig + B_exp) + n²ρ)`
bits. Each `qᵢ` has `O(ρ)` bits, and the common exponent `γ` has `O(B_exp + log(B_sig + ρ + 1))`
bits. The algorithm does not require a supplied condition-number bound."

**Formalization Note.**
* "Deterministic algorithm" and "bit operations": one deterministic multitape Turing machine
  `M : IntMul.MultitapeTM` (reused public model), chosen before the input, with its steps counted.
* The input is the word `encInst I` (`n`, `E`, `m`, the nonzero entries with their indices in any
  order, the right-hand side with zero entries included); it contains no `κ`, `B_sig` or `B_exp`.
  The output is the word `q₁ # ⋯ # qₙ # γ` on the output tape when the machine halts.
* `Õ(T)` is `C · T · lg(2 + n + B_sig + B_exp + ρ)^K` with one `C > 0` and one `K` for all inputs,
  and no threshold on `n`; `O(·)` is `C · (·)` with the same `C`.
* Storage is `SpaceWithin`: no head (input tape included) passes cell `σ` during the run.
* `1 ≤ n` excludes the empty system. `ρ` uses the spectral condition number `kappa2`. -/
theorem theorem_1_1 :
    ∃ (M : IntMul.MultitapeTM) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (I : FloatInstance) (Bsig Bexp : ℕ), I.WellFormed → 1 ≤ I.n → 1 ≤ I.E → I.A.det ≠ 0 →
        (∀ t ∈ I.entries, bitsInt t.2.2.1 ≤ Bsig ∧ bitsInt t.2.2.2 ≤ Bexp) →
        (∀ i, bitsInt (I.rhs i).1 ≤ Bsig ∧ bitsInt (I.rhs i).2 ≤ Bexp) →
        ∃ (q : Fin I.n → ℤ) (γ : ℤ) (t : ℕ),
          M.HaltsWithOutputW I.encInst t (encOutput q γ) ∧
          (t : ℝ) ≤ C * (((I.m + I.n) * (Bsig + Bexp) + I.m * I.n * rho I.n I.E (kappa2 I.A) : ℕ) : ℝ)
            * polylog K (2 + I.n + Bsig + Bexp + rho I.n I.E (kappa2 I.A)) ∧
          SpaceWithin M I.encInst t
            (C * (((I.m + I.n) * (Bsig + Bexp) + I.n ^ 2 * rho I.n I.E (kappa2 I.A) : ℕ) : ℝ)
              * polylog K (2 + I.n + Bsig + Bexp + rho I.n I.E (kappa2 I.A))) ∧
          norm2 (I.A *ᵥ (fun i => floatVal (q i) γ) - I.b) ≤ (2 : ℝ) ^ (-(I.E : ℤ)) * norm2 I.b ∧
          (∀ i, (bitsInt (q i) : ℝ) ≤ C * rho I.n I.E (kappa2 I.A)) ∧
          (bitsInt γ : ℝ) ≤ C * ((Bexp : ℝ) + Real.logb 2 ((Bsig : ℝ) + rho I.n I.E (kappa2 I.A) + 1)) := by sorry

end KelnerLinSolve
