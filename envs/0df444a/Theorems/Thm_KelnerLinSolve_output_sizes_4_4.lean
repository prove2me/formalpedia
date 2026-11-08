-- Prove2me | Theorems.Thm_KelnerLinSolve_output_sizes_4_4
-- name    : KelnerLinSolve.output_sizes_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:48.972823+00:00
-- url     : https://prove2.me/theorems/78101ca4-f4b0-4fbd-b317-4c62db82944a
-- title:
--   §4.4 — output sizes: each $q_i$ has $O(\rho)$ bits, $|\gamma|\le2^{B_{\mathrm{exp}}+1}+2B_{\mathrm{sig}}+p$
-- statement:
--   Let $n\ge1$, $\ell = \lceil\log_2n\rceil$, $p = E+2\ell+2$, $P = 2^p$, $\varepsilon = 2^{-E}$, and let $y\in\mathbb R^n$ pass the test $8n^2(\|y\|_\infty+1)\le\varepsilon2^h$. Let $q_i = \mathrm{round}(Py_i)$ for a rounding to nearest.
--
--   1. $\|y\|_\infty+1\le\varepsilon2^h/(8n^2)$ and $|q_i|\le P\|y\|_\infty+1/2$.
--   2. For every constant $c>0$ there is $C$ such that, whenever $h\le c\rho$ with $\rho = 1+E+\lceil\log_2\kappa\rceil+\lceil\log_2(n+1)\rceil$, $\kappa\ge1$, $E,h\ge1$, every $q_i$ has at most $C\rho$ bits.
--   3. For a well-formed instance as in Theorem 1.1 (with $A$ nonsingular, $b\ne0$, every entry $u2^e$ with $\mathrm{bits}(u)\le B_{\mathrm{sig}}$, $\mathrm{bits}(e)\le B_{\mathrm{exp}}$) and $\gamma = \beta-\alpha-p$,
--
--   $$
--   |\gamma|\le2^{B_{\mathrm{exp}}+1}+2B_{\mathrm{sig}}+p.
--   $$
--
--   4. There is an absolute $C$ with $\mathrm{bits}(\gamma)\le C\,(B_{\mathrm{exp}}+\log_2(B_{\mathrm{sig}}+\rho+1))$ for all such instances, $\rho$ taken at $\kappa_2(A)$.
--
--   These give the output-size clauses of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: κ = κ₂(A) in ρ (item 2) → any real κ ≥ 1; reason: κ₂(A) ≥ 1 for nonsingular A, so this specializes
--   - reading: since p = O(E + log(n + 1)) and h = O(ρ) → a hypothesis h ≤ cρ for any c > 0, with C depending on c; p is the defined E + 2ℓ + 2; reason: h = O(ρ) is the premise the page imports from the trial analysis
--   - encoding: y the accepted trial's vector → any real vector passing the test (8); reason: the accepted y is one; the bounds use only the test
--   - encoding: n ≥ 1 (implicit) → hypothesis 1 ≤ n; reason: excludes the empty system, where the division by 8n² has no meaning
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §4.4, p.14; p, P, q_i, γ from (12), §4.2, p.13

import Mathlib
import Definitions.Def_KelnerLinSolve_FloatInstance
import Definitions.Def_KelnerLinSolve_kappa2
import Definitions.Def_KelnerLinSolve_trialY

namespace KelnerLinSolve

/-- **§4.4, sizes of the output integers**, Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit
Operations*, STOC 2027 submission (sha256 d1af55cb…), p.14. "Finally, acceptance gives
`‖y‖_∞ + 1 ≤ ε2^h/(8n²)`, and `|qᵢ| ≤ P‖y‖_∞ + 1/2`. Since `p = O(E + log(n + 1))` and `h = O(ρ)`,
each `qᵢ` has `O(ρ)` bits. The definitions of `α, β` give `|γ| ≤ 2^{B_exp+1} + 2B_sig + p`, so its
encoding has `O(B_exp + log(B_sig + ρ + 1))` bits." Here `ℓ = ⌈log₂ n⌉`, `p = E + 2ℓ + 2`,
`P = 2^p`, `qᵢ = round(Pyᵢ)` and `γ = β − α − p` ((12), §4.2, p.13), `ε = 2^{−E}`.

Four conjuncts: (a) acceptance gives the first bound and `|qᵢ| ≤ P‖y‖_∞ + 1/2`; (b) for every
constant `c`, there is `C` such that, whenever the accepted precision satisfies `h ≤ cρ`, every
`qᵢ` has at most `Cρ` bits; (c) `|γ| ≤ 2^{B_exp+1} + 2B_sig + p` for an instance as in Theorem 1.1
with `b ≠ 0`; (d) `bits(γ) ≤ C (B_exp + log₂(B_sig + ρ + 1))` for one absolute `C`.

**Formalization Note.** In (a) and (b) `y` is any real vector that passes the test (8); `rnd` is any
rounding to nearest. In (b), `ρ = 1 + E + ⌈log₂ κ⌉ + ⌈log₂(n+1)⌉` for any `κ ≥ 1` (the page's
`κ = κ₂(A) ≥ 1`). -/
theorem output_sizes_4_4 :
    (∀ {n : ℕ} (E h : ℕ) (y : Fin n → ℝ) (rnd : ℝ → ℤ), 1 ≤ n → IsNearestRounding rnd →
      8 * (n : ℝ) ^ 2 * (infNorm y + 1) ≤ (2 : ℝ) ^ (-(E : ℤ)) * (2 : ℝ) ^ h →
        infNorm y + 1 ≤ (2 : ℝ) ^ (-(E : ℤ)) * (2 : ℝ) ^ h / (8 * (n : ℝ) ^ 2) ∧
        ∀ i, |(rnd ((2 : ℝ) ^ (E + 2 * Nat.clog 2 n + 2) * y i) : ℝ)|
          ≤ (2 : ℝ) ^ (E + 2 * Nat.clog 2 n + 2) * infNorm y + 1 / 2) ∧
    (∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (E h : ℕ) (κ : ℝ) (y : Fin n → ℝ) (rnd : ℝ → ℤ), 1 ≤ n → 1 ≤ E → 1 ≤ h → 1 ≤ κ →
        IsNearestRounding rnd →
        8 * (n : ℝ) ^ 2 * (infNorm y + 1) ≤ (2 : ℝ) ^ (-(E : ℤ)) * (2 : ℝ) ^ h →
        (h : ℝ) ≤ c * rho n E κ →
          ∀ i, (bitsInt (rnd ((2 : ℝ) ^ (E + 2 * Nat.clog 2 n + 2) * y i)) : ℝ) ≤ C * rho n E κ) ∧
    (∀ (I : FloatInstance) (Bsig Bexp : ℕ), I.WellFormed → 1 ≤ I.n → 1 ≤ I.E → I.A.det ≠ 0 →
      I.b ≠ 0 →
      (∀ t ∈ I.entries, bitsInt t.2.2.1 ≤ Bsig ∧ bitsInt t.2.2.2 ≤ Bexp) →
      (∀ i, bitsInt (I.rhs i).1 ≤ Bsig ∧ bitsInt (I.rhs i).2 ≤ Bexp) →
        |I.betaExp - I.alphaExp - ((I.E + 2 * Nat.clog 2 I.n + 2 : ℕ) : ℤ)|
          ≤ 2 ^ (Bexp + 1) + 2 * (Bsig : ℤ) + ((I.E + 2 * Nat.clog 2 I.n + 2 : ℕ) : ℤ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (I : FloatInstance) (Bsig Bexp : ℕ), I.WellFormed → 1 ≤ I.n → 1 ≤ I.E →
      I.A.det ≠ 0 → I.b ≠ 0 →
      (∀ t ∈ I.entries, bitsInt t.2.2.1 ≤ Bsig ∧ bitsInt t.2.2.2 ≤ Bexp) →
      (∀ i, bitsInt (I.rhs i).1 ≤ Bsig ∧ bitsInt (I.rhs i).2 ≤ Bexp) →
        (bitsInt (I.betaExp - I.alphaExp - ((I.E + 2 * Nat.clog 2 I.n + 2 : ℕ) : ℤ)) : ℝ)
          ≤ C * ((Bexp : ℝ) + Real.logb 2 ((Bsig : ℝ) + rho I.n I.E (kappa2 I.A) + 1))) := by sorry

end KelnerLinSolve
