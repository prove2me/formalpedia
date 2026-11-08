-- Prove2me | Theorems.Thm_KelnerLinSolve_conversion_4_1
-- name    : KelnerLinSolve.conversion_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:42.402904+00:00
-- url     : https://prove2.me/theorems/ae9a802c-cc4e-4d8b-9a0d-32e320bd9a47
-- title:
--   §4.1 — conversion of normalized entries: small entries round to zero, $|k| = O(B_{\mathrm{sig}}+h)$, $|C_{ij}|,|d_i|\le S$
-- statement:
--   Let $u2^e$ be an entry with $u\neq0$, normalized by an exponent $\alpha$ with $e+\mathrm{len}(u)\le\alpha$, so that $\eta = e-\alpha$, and let $h\ge1$ be the precision and $k=\eta+h$.
--
--   1. If $k+\mathrm{len}(u)\le-1$ then $|u2^k|<1/2$, and every rounding to nearest maps $u2^k$ to $0$.
--   2. There is an absolute constant $C$ such that, otherwise, $|k|\le C(B_{\mathrm{sig}}+h)$ whenever $\mathrm{bits}(u)\le B_{\mathrm{sig}}$.
--   3. For a well-formed instance as in Theorem 1.1 with $b\neq0$ and $S=2^h$, the converted data $C=\mathrm{round}(SA_0)$, $d=\mathrm{round}(Sb_0)$ have entries of magnitude at most $S$, and $C$ has at most $m$ nonzero entries.
--
--   So conversion needs only $O(B_{\mathrm{sig}}+h)$ significand bits per entry, and entries far below the threshold are detected from exponents alone.
--
--   Differences from the source:
--   - generalization: η = e − α with α the maximum of e' + len(u') over the entries → any α with e + len(u) ≤ α; reason: every entry satisfies this for the page's α (or β), so the statement specializes
--   - reading: the converted entry is zero → every rounding to nearest maps u2^k to 0; reason: |u2^k| < 1/2 makes the nearest integer unique
--   - encoding: O(B_sig + h) → one absolute constant C; reason: definition of O
--   - encoding: the standing setting of §4.1 in the sentence on C, d → hypotheses `WellFormed`, 1 ≤ n, det A ≠ 0, b ≠ 0 in item 3; reason: the page assumes them; 1 ≤ n excludes the empty system
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §4.1, pp.12–13

import Mathlib
import Definitions.Def_KelnerLinSolve_FloatInstance
import Definitions.Def_KelnerLinSolve_trialY

namespace KelnerLinSolve

/-- **§4.1, conversion of normalized entries to integers**, Kelner, *Solving Linear Systems in
Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission (sha256 d1af55cb…), pp.12–13. "For a normalized
entry `u2^η`, let `k = η + h`. If `k + len(u) ≤ −1`, then `|u2^k| < 1/2` and the converted entry is
zero; this is detected by comparing encoded exponents. Otherwise `|k| = O(B_sig + h)`: a nonnegative
`k` calls for a left shift, while a negative `k` calls for division by `2^{−k}` and rounding."
Together with the preceding sentence (pp.12–13): "The entries of `C, d` have magnitude at most `S`,
hence `O(h)` bits, and `C` has at most `m` nonzeros."

Three conjuncts, for an entry `u 2^e` (`u ≠ 0`) normalized by an exponent `α ≥ e + len(u)` (so
`η = e − α`) and a precision `h ≥ 1`: (a) if `k + len(u) ≤ −1` then `|u 2^k| < 1/2` and every
rounding to nearest maps `u 2^k` to `0`; (b) otherwise `|k| ≤ C (B_sig + h)` for one absolute `C`
whenever `bits(u) ≤ B_sig`; (c) for an instance as in Theorem 1.1 with `b ≠ 0`, `C = round(SA₀)` and
`d = round(Sb₀)` have entries of magnitude at most `S = 2^h`, and `C` has at most `m` nonzero entries.

**Formalization Note.** The normalizing exponent is any `α` with `e + len(u) ≤ α` (`α` of §4.1 for an
entry of `A`, `β` for an entry of `b`). `len` is `lenInt`; `u 2^k` is `floatVal u k`. -/
theorem conversion_4_1 :
    (∀ (u e α : ℤ) (h : ℕ), u ≠ 0 → 1 ≤ h → e + (lenInt u : ℤ) ≤ α →
      (e - α) + (h : ℤ) + (lenInt u : ℤ) ≤ -1 →
        |floatVal u ((e - α) + h)| < 1 / 2 ∧
          ∀ rnd : ℝ → ℤ, IsNearestRounding rnd → rnd (floatVal u ((e - α) + h)) = 0) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (u e α : ℤ) (h Bsig : ℕ), u ≠ 0 → 1 ≤ h → e + (lenInt u : ℤ) ≤ α →
      bitsInt u ≤ Bsig → ¬ ((e - α) + (h : ℤ) + (lenInt u : ℤ) ≤ -1) →
        (|(e - α) + (h : ℤ)| : ℝ) ≤ C * ((Bsig : ℝ) + h)) ∧
    (∀ (I : FloatInstance) (h : ℕ) (rnd : ℝ → ℤ), I.WellFormed → 1 ≤ I.n → I.A.det ≠ 0 → I.b ≠ 0 →
      1 ≤ h → IsNearestRounding rnd →
      let Cm : Fin I.n → Fin I.n → ℤ := fun i j => rnd ((2 : ℝ) ^ h * ((2 : ℝ) ^ (-I.alphaExp) * I.A i j))
      let d : Fin I.n → ℤ := fun i => rnd ((2 : ℝ) ^ h * ((2 : ℝ) ^ (-I.betaExp) * I.b i))
      (∀ i j, |(Cm i j : ℝ)| ≤ (2 : ℝ) ^ h) ∧ (∀ i, |(d i : ℝ)| ≤ (2 : ℝ) ^ h) ∧
        (Finset.univ.filter fun p : Fin I.n × Fin I.n => Cm p.1 p.2 ≠ 0).card ≤ I.m) := by sorry

end KelnerLinSolve
