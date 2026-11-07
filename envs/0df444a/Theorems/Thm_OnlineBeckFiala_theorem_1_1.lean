-- Prove2me | Theorems.Thm_OnlineBeckFiala_theorem_1_1
-- name    : OnlineBeckFiala.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:08.082064+00:00
-- url     : https://prove2.me/theorems/6539939d-5b2f-460e-a9d7-eaf6c4b85434
-- title:
--   Theorem 1.1 (Online Beck–Fiala) — online signs with prefix discrepancy $\le C_\eta\sqrt d$ except with probability $C_\eta T e^{-c_\eta d/\log^{2+\eta}(ed)}$
-- statement:
--   For every fixed $\eta>0$ there are constants $c_\eta,C_\eta>0$ with the following property. Let $n\ge0$ and $d\ge2$ be integers. There is a randomized online signing algorithm such that, for every $T$ and every fixed sequence $a_1,\dots,a_T\in[-1,1]^n$ with at most $d$ nonzero coordinates in each vector,
--   $$P\Bigl\{\max_{t\le T}\Bigl\|\sum_{s\le t}\varepsilon_sa_s\Bigr\|_\infty>C_\eta\sqrt d\Bigr\}\le C_\eta T\exp\Bigl[-\frac{c_\eta d}{\log^{2+\eta}(ed)}\Bigr].\qquad(2)$$
--   Consequently, there are constants $C,C',T_0>0$, depending only on $\eta$, such that whenever $T\ge T_0$ and
--   $$d\ge C(\log T)(\log\log T)^{2+\eta},\qquad(3)$$
--   the prefix discrepancy of the same algorithm is at most $C'\sqrt d$ with probability at least $1-T^{-1}$.
--
--   The signs $\varepsilon_t\in\{-1,1\}$ are chosen online, each from $a_1,\dots,a_t$ and the algorithm's private randomness, against an oblivious adversary. The theorem gives the conjectured $O(\sqrt d)$ online prefix discrepancy down to sparsity $d\approx\log T\,(\log\log T)^{2+\eta}$, improving the previous online bound $O(\sqrt{d\log T})$; the case $d=n$ gives an $O(\sqrt n)$ online prefix bound in the Spencer setting.
--
--   **Formalization Note** All constants are chosen before $n$ and $d$; the algorithm is chosen after $n,d$ and before $T$, and one algorithm serves both clauses. The constant $C$ of (3) is named `C₃`. $(\log\log T)^{2+\eta}$ is a real power; for $T<e^e$ its base is $\le0$ and Lean's real power takes a default value, but $T_0$ is existential, so a proof may take $T_0$ large.
--
--   Differences from the source:
--   - encoding: a randomized online algorithm choosing εt from a1, …, at against an oblivious adversary → an OnlineSigner n: a probability space, signs ±1, an online clause, measurability, and a law independent of the input; reason: the structure states each clause of the p.1 model
--   - encoding: a1, …, aT and max over t ≤ T → a 0, …, a (T−1) of a sequence ℕ → ℝ^n, hypotheses on s < T only, ∃ t < T; reason: 0-based times; later entries cannot affect εt for t < T by the online clause
--   - reading: "Consequently … the prefix discrepancy is at most C′√d" → one ∃ alg serving (2) and the high-probability clause; reason: the clause speaks of the algorithm just given; separate algorithms would be weaker
--   - reading: constants depending only on η; n never quantified → c, C, C₃, C′, T₀ chosen before n and d; reason: the constants are introduced before "Let d ≥ 2" and the text never lets them depend on n; Corollary 1.3's d = n needs it
--   - encoding: the constant C of (3) → C₃; reason: the letter C is already C_η
--   - encoding: (log log T)^{2+η} and the probability bound → Real.rpow with Mathlib's default below T = e^e; ENNReal.ofReal of the right side of (2); reason: T₀ is existential, so the default range is never forced; the right side of (2) is nonnegative
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.2, Theorem 1.1, eqs. (2), (3)

import Mathlib
import Definitions.Def_OnlineBeckFiala_OnlineSigner

open MeasureTheory

namespace OnlineBeckFiala

/-- **Theorem 1.1 (Online Beck–Fiala), p.2.** Altschuler, Tikhomirov, *Online Beck–Fiala Down to
Logarithmic Sparsity*, arXiv:2607.14238 (held version, sha256 5a1529d2…): "For every fixed η > 0
there are constants c_η, C_η > 0 with the following property. Let d ≥ 2. There is a randomized online
algorithm such that, for every T and every fixed sequence a1, . . . , aT ∈ [−1, 1]^n with at most d
nonzero coordinates in each vector,
P{max_{t≤T} ‖∑_{s≤t} εs as‖∞ > C_η √d} ≤ C_η T exp[−c_η d / log^{2+η}(ed)]. (2)
Consequently, there are constants C, C′, T0 > 0, depending only on η, such that, whenever T ≥ T0 and
d ≥ C (log T)(log log T)^{2+η}, (3)
the prefix discrepancy is at most C′√d with probability at least 1 − T^{−1}."

**Formalization Note.**
* The algorithm is an `OnlineSigner n`: signs `±1`, `ε_t` a function of `a_1, …, a_t` and private
  randomness whose law does not depend on the input (oblivious adversary). One algorithm, chosen
  after `n` and `d` and before `T`, serves both clauses.
* All constants are chosen before `n` and `d` (they depend only on `η`). The constant `C` of (3) is
  named `C₃` here, to keep it apart from `C_η`.
* Times are 0-based: `a 0, …, a (T-1)`, prefixes `t < T`; the box and sparsity hypotheses are on
  `a s` for `s < T` only (`IsSparseBox`). `‖·‖` on `Fin n → ℝ` is the sup norm.
* `log^{2+η}(ed)` is `(log (e·d))^(2+η)` and `(log log T)^{2+η}` a real power; for `T < e^e` the base
  `log log T` is `≤ 0` and the real power takes Mathlib's junk value, but `T₀` is existential so a
  proof may take it large. The bound (2) is compared through `ENNReal.ofReal`. -/
theorem theorem_1_1 :
    ∀ η : ℝ, 0 < η → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ C₃ C' T₀ : ℝ, 0 < C₃ ∧ 0 < C' ∧ 0 < T₀ ∧
      ∀ (n d : ℕ), 2 ≤ d → ∃ alg : OnlineSigner n,
        (∀ (T : ℕ) (a : ℕ → (Fin n → ℝ)), IsSparseBox d T a →
          alg.P {ω | ∃ t < T, C * Real.sqrt d < ‖prefixSum alg a t ω‖} ≤
            ENNReal.ofReal
              (C * T * Real.exp (-(c * d) / (Real.log (Real.exp 1 * d)) ^ (2 + η)))) ∧
        (∀ T : ℕ, T₀ ≤ T → C₃ * Real.log T * (Real.log (Real.log T)) ^ (2 + η) ≤ d →
          ∀ a : ℕ → (Fin n → ℝ), IsSparseBox d T a →
            1 - (T : ENNReal)⁻¹ ≤ alg.P {ω | ∀ t < T, ‖prefixSum alg a t ω‖ ≤ C' * Real.sqrt d}) := by sorry

end OnlineBeckFiala
