-- Prove2me | Theorems.Thm_KelnerLinSolve_theorem_2_3
-- name    : KelnerLinSolve.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:07.520213+00:00
-- url     : https://prove2.me/theorems/a07c87bc-7d85-4f8c-9c5e-9f23ac4017ca
-- title:
--   Theorem 2.3 — fast rational reconstruction: uniqueness and $O(\mathsf M(s)\log s)$ recovery
-- statement:
--   Let $Q, v, N, D$ be integers with $Q\ge2$, $0\le v<Q$, $N,D\ge1$ and $Q>2ND$, and put $s = \lceil\log_2(Q+1)\rceil$.
--
--   1. **Uniqueness.** There is at most one reduced fraction $a/c$ with $|a|\le N$, $1\le c\le D$, $\gcd(c,Q)=1$ and $a\equiv vc\pmod Q$.
--   2. **Recovery with a given multiplier.** For every multitape machine that multiplies $s$-bit integers within $T(s)$ steps, $T$ regular, there are a multitape machine and a constant $C$ such that, on input $Q\#v\#N\#D$, whenever the fraction exists the machine halts with output $a\#c$ within $C\,T(s)\,\mathrm{lg}\,s$ steps.
--   3. **Unconditional bound.** There are a multitape machine and constants $C, K$ with the same behaviour within $C\,s\,\mathrm{lg}(s)^K = \tilde O(\log Q)$ steps.
--
--   The paper cites this result (Wang–Guy–Davenport, Collins–Encarnación, Monagan, Wang–Pan, Pan–Wang) and proves only uniqueness. It is the reconstruction step of Dixon's algorithm.
--
--   Differences from the source:
--   - encoding: integers Q, v, N, D → natural numbers; reason: the hypotheses force them nonnegative
--   - encoding: reduced fraction a/c with gcd(c, Q) = 1, a ≡ vc (mod Q) → a rational r with `RatCongr r v Q`; reason: same fractions
--   - reading: M(s), the bit complexity of multiplying two s-bit integers → the time bound T of any multiplication machine (`IntMul.MultipliesAt`), assumed regular (T(s)/s nondecreasing, T(2s) ≤ 4T(s)), plus an unconditional Õ clause; reason: the page leaves M(s) unregulated; these are the standard conditions behind O(M(s) log s) (paper.md decision 6)
--   - reading: recovered deterministically in … bit operations → a multitape machine reading Q#v#N#D in binary and halting with a#c; unconstrained on other inputs; reason: the machine model of the goal (paper.md decision 2)
--   - encoding: s = ⌈log₂(Q + 1)⌉ → `Nat.size Q`; reason: equal for every natural Q
--   - encoding: log s in O(M(s) log s) → `IntMul.lg s` = max(⌈log₂ s⌉, 1); reason: same up to a constant for s ≥ 2, and the hypotheses force s ≥ 2
--   - reading: Õ(log Q) → C·s·lg(s)^K with one C, K for all inputs; reason: §1.1: Õ suppresses polylogarithmic factors, and s is the bit length of Q
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Theorem 2.3, p.7

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_MultitapeWords
import Definitions.Def_KelnerLinSolve_encInt
import Definitions.Def_KelnerLinSolve_RatCongr
import Definitions.Def_KelnerLinSolve_SpaceWithin

namespace KelnerLinSolve

/-- **Theorem 2.3 (Fast rational reconstruction)**, Kelner, *Solving Linear Systems in
Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission (sha256 d1af55cb…), p.7 (cited by the paper from
Wang–Guy–Davenport, Collins–Encarnación, Monagan, Wang–Pan, Pan–Wang). "Let `Q, v, N, D` be integers
with `Q ≥ 2`, `0 ≤ v < Q`, and `N, D ≥ 1` such that `Q > 2ND`. There is at most one reduced fraction
`a/c` satisfying `|a| ≤ N, 1 ≤ c ≤ D, gcd(c, Q) = 1, a ≡ vc (mod Q)`. If such a fraction exists, it
can be recovered deterministically in `O(M(s) log s)` bit operations, where `s = ⌈log₂(Q + 1)⌉` and
`M(s)` is the bit complexity of multiplying two `s`-bit integers. In particular, `M(s) = Õ(s)`, …
hence the running time is `Õ(log Q)`."

Three conjuncts: (a) uniqueness; (b) for every multiplication machine with a regular time bound
`T`, a reconstruction machine running in `C · T(s) · lg s` steps; (c) a reconstruction machine
running in `C · s · lg(s)^K` steps (`Õ(log Q)`).

**Formalization Note.** `Q, v, N, D` are naturals (the hypotheses force them nonnegative). A reduced
fraction `a/c` with `c ≥ 1` is a rational `r` (`r.num = a`, `r.den = c`); `gcd(c, Q) = 1` and
`a ≡ vc` are `RatCongr r v Q`. `s = Nat.size Q = ⌈log₂(Q + 1)⌉`. The machine reads
`Q # v # N # D` in binary and, when the fraction exists, halts with `a # c` (signed `a`, unsigned `c`)
on its output tape; on other inputs it is unconstrained. `M(s)` is read as the bound `T` of a given
multiplication machine (`IntMul.MultipliesAt`), assumed regular (`IsRegularTimeBound`). -/
theorem theorem_2_3 :
    (∀ Q v N D : ℕ, 2 ≤ Q → v < Q → 1 ≤ N → 1 ≤ D → 2 * N * D < Q →
      ∀ r r' : ℚ,
        (|r.num| ≤ N ∧ r.den ≤ D ∧ RatCongr r v Q) →
        (|r'.num| ≤ N ∧ r'.den ≤ D ∧ RatCongr r' v Q) → r = r') ∧
    (∀ (Mul : IntMul.MultitapeTM) (T : ℕ → ℝ), (∀ s : ℕ, 1 ≤ s → IntMul.MultipliesAt Mul s (T s)) →
      IsRegularTimeBound T →
      ∃ (Rec : IntMul.MultitapeTM) (C : ℝ), 0 < C ∧
        ∀ Q v N D : ℕ, 2 ≤ Q → v < Q → 1 ≤ N → 1 ≤ D → 2 * N * D < Q →
          ∀ r : ℚ, |r.num| ≤ N → r.den ≤ D → RatCongr r v Q →
            ∃ t : ℕ, (t : ℝ) ≤ C * T (Nat.size Q) * (IntMul.lg (Nat.size Q) : ℝ) ∧
              Rec.HaltsWithOutputW (IntMul.joinSep [encNat Q, encNat v, encNat N, encNat D]) t
                (IntMul.joinSep [encInt r.num, encNat r.den])) ∧
    (∃ (Rec : IntMul.MultitapeTM) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ Q v N D : ℕ, 2 ≤ Q → v < Q → 1 ≤ N → 1 ≤ D → 2 * N * D < Q →
          ∀ r : ℚ, |r.num| ≤ N → r.den ≤ D → RatCongr r v Q →
            ∃ t : ℕ, (t : ℝ) ≤ C * (Nat.size Q : ℝ) * polylog K (Nat.size Q) ∧
              Rec.HaltsWithOutputW (IntMul.joinSep [encNat Q, encNat v, encNat N, encNat D]) t
                (IntMul.joinSep [encInt r.num, encNat r.den])) := by sorry

end KelnerLinSolve
