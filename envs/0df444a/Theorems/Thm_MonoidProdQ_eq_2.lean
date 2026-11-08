-- Prove2me | Theorems.Thm_MonoidProdQ_eq_2
-- name    : MonoidProdQ.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:57:48.962919+00:00
-- url     : https://prove2.me/theorems/8babec14-6c60-4fb2-8bca-b40a06dd999c
-- title:
--   Eq. (2) (adversary tightness): $Q_{1/3}(f)=\Theta(\mathrm{ADV}^{\pm}(f))$ with universal constants
-- statement:
--   There are universal constants $c,C>0$ such that for every finite nonempty index set $I$, every finite input alphabet $\Sigma$, every finite nonempty output alphabet $O$, every promise domain $D\subseteq\Sigma^I$ and every function $f$ with values in $O$,
--
--   $$c\,\mathrm{ADV}^{\pm}(f)\ \le\ Q_{1/3}(f)\ \le\ C\,\mathrm{ADV}^{\pm}(f).$$
--
--   This is the general adversary theorem (Høyer–Lee–Špalek for the lower bound, Reichardt and Lee–Mittal–Reichardt–Špalek–Szegedy for the upper bound), which the paper cites and uses as the bridge between adversary values and query complexity in both directions.
--
--   Differences from the source:
--   - reading: universal implicit constants → one pair $c,C>0$ chosen before $I,\Sigma,O,D,f$; reason: the literal meaning of universal constants
--   - encoding: every function with finite input and output alphabets → hypotheses `Nonempty I` and `Nonempty Out`; reason: with no positions the platform's query register is empty and no algorithm exists, and with an empty output type there is no output map; both are degenerate cases the paper never uses (its inputs have $n\ge1$ positions and $f$ takes values)
--   - encoding: $\mathrm{ADV}^{\pm}$ and $Q_{1/3}$ as numbers → `ADV±` in `ℝ≥0∞`, $Q_{1/3}$ in `ℕ∞` (cast to `ℝ≥0∞`); reason: Lean convention; suprema and infima are never junk values, and both are finite in every instance
--   - encoding: a query to index $i$ returns the entire letter $x_i$ → the platform's standard oracle $|i,y\rangle\mapsto|i,y+e_{x_i}\rangle$ with the one-hot code $e_{x_i}\in(\mathbb Z/2)^\Sigma$; reason: the paper fixes no encoding; injective encodings change query counts by at most a factor two, absorbed by the universal constants
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Eq. (2), p.24 (cited from [Rei11, LMR+11])

import Definitions.Def_MonoidProdQ_advPm
import Definitions.Def_MonoidProdQ_Q13

open scoped ENNReal

universe u v w

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Eq. (2), p.24 (adversary tightness, cited from [Rei11, LMR+11]): "under our fixed
bounded-error convention, for every function with finite input and output alphabets,
Q_{1/3}(f) = Θ(ADV±(f)), with universal implicit constants". One pair of constants `c, C > 0`,
chosen before the index set, the alphabets, the promise domain and the function, gives
`c · ADV±(f) ≤ Q_{1/3}(f) ≤ C · ADV±(f)`, both directions.

**Formalization Note.** The index set and the output alphabet are nonempty: with no index the
platform's query register `I × κ` is empty and no algorithm exists at all, and with an empty
output type there is no output map; neither degenerate case is a function the paper considers
(its inputs have `n ≥ 1` positions and `f` takes values). -/
theorem eq_2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (I : Type u) (Sig : Type v) (Out : Type w) [Fintype I] [DecidableEq I] [Nonempty I]
        [Fintype Sig] [DecidableEq Sig] [Fintype Out] [DecidableEq Out] [Nonempty Out]
        (f : (I → Sig) → Out) (D : Finset (I → Sig)),
        ENNReal.ofReal c * advPm f D ≤ (Q13 f D : ℝ≥0∞) ∧
          (Q13 f D : ℝ≥0∞) ≤ ENNReal.ofReal C * advPm f D := by sorry

end MonoidProdQ
