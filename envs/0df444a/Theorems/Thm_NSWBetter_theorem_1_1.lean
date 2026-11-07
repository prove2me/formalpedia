-- Prove2me | Theorems.Thm_NSWBetter_theorem_1_1
-- name    : NSWBetter.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:53:03.763748+00:00
-- url     : https://prove2.me/theorems/467a65e3-4287-4203-b14e-555f5856ace7
-- title:
--   Theorem 1.1 — a randomized polynomial-time $(e^{1/e}-c)$-approximation for Nash social welfare
-- statement:
--   There are a constant $c>0$, a polynomial $p$ and a randomized polynomial-time algorithm $A$ (a deterministic polynomial-time algorithm reading a uniformly random string of $p(|\langle I\rangle|)$ fair coins) such that for every instance $I$ with additive valuations given by nonnegative rationals, the allocation $X$ output by $A$ satisfies
--   $$\mathrm{NSW}(Y)\le\bigl(e^{1/e}-c\bigr)\,\mathbb E[\mathrm{NSW}(X)]\qquad\text{for every allocation }Y,$$
--   that is, $\mathbb E[\mathrm{NSW}(X)]\ge\mathrm{NSW}(I)/(e^{1/e}-c)$. Here $\mathrm{NSW}(X)=(\prod_iv_i(X_i))^{1/n}$ and allocations are $n$-subpartitions of the goods.
--
--   This is the first improvement over the approximation factor $e^{1/e}$ for maximizing Nash social welfare under additive valuations.
--
--   Differences from the source:
--   - reading: "efficient randomized algorithm" → a polynomial $p$ and a `Turing.TM2ComputableInPolyTime` map of (encoded instance, coin string), the guarantee holding for the average over all coin strings of length $p(|\langle I\rangle|)$; reason: the standard model of randomized polynomial time; the rational-probability steps of the paper (dependent rounding p.38, ST rounding p.16) are sampled with fair coins to accuracy $2^{-\mathrm{poly}}$, and since $\mathrm{NSW}(X)\le\mathrm{NSW}(I)$ the loss is absorbed by the slack between $c^*/2$ and $c$ on p.48
--   - reading: "$(e^{1/e}-c)$-approximation" of a randomized algorithm → $\mathrm{NSW}(Y)\le(e^{1/e}-c)\,\mathbb E[\mathrm{NSW}(X)]$ for every allocation $Y$; reason: the definition on p.9 applied in expectation, as the proof concludes on p.48; the multiplicative form avoids a division and the maximum over allocations
--   - encoding: valuations in $\mathbb R_{\ge0}$, agents, goods, allocations, outputs → nonnegative rationals in binary, `Fin n`, `Fin m`, `Fin m → Option (Fin n)`, outputs as lists of naturals decoded totally; reason: an algorithm's input is finite; Lean convention; same instances
--   - encoding: "efficient" (polynomial time) → `Turing.TM2ComputableInPolyTime` over fixed binary encodings over `OnlineCRS.Combine.Sym`; reason: Mathlib's Turing-machine model; binary numbers make the input length the bit size
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 1.1, p.3 (proof p.48)

import Mathlib
import Definitions.Def_ReserveLB_encListNat
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_Inst_WellFormed
import Definitions.Def_NSWBetter_Alloc
import Definitions.Def_NSWBetter_nsw
import Definitions.Def_NSWBetter_decodeAlloc
import Definitions.Def_NSWBetter_encInst
import Definitions.Def_NSWBetter_encInstCoins
import Definitions.Def_NSWBetter_coinAvg

namespace NSWBetter

/-- **Theorem 1.1 — a better-than-e^(1/e) approximation for Nash social welfare.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 1.1, p.3 (restated and proved p.48): "There exists an efficient randomized (e^(1/e) − c)-approximation algorithm for maximizing Nash social welfare when agents have additive valuations, for some constant c > 0." Approximation, p.9: "An allocation X is said to be an α-approximation (α ≥ 1) of the max Nash welfare for some instance I if NSW(X) ≥ (1/α)NSW(I)"; the proof (p.48) concludes `E[NSW(X)] ≥ NSW(I)/e^(1/e − c∗/2)`.

There are a constant `c > 0`, a polynomial `p` and a Turing machine `A`, polynomial time in the binary encoding of `(I, coins)`, such that for every instance `I` with nonnegative rational additive valuations and every allocation `Y`, `NSW(Y) ≤ (e^(1/e) − c) · E_w[NSW(X_w)]`, where `X_w` is the allocation output on coin string `w` and `w` is uniform of length `p(|enc I|)`.

**Formalization Note.** Randomness is a uniform coin string of fixed polynomial length given to a deterministic machine. Outputs are lists of naturals decoded totally into `n`-subpartitions (`decodeAlloc`). The comparator is every allocation, so the bound is against `NSW(I)` without a maximum or a division. -/
theorem theorem_1_1 :
    ∃ c : ℝ, 0 < c ∧
    ∃ (p : Polynomial ℕ) (A : Inst × List Bool → List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encInstCoins ReserveLB.encListNat A) ∧
      ∀ I : Inst, I.WellFormed → ∀ Y : Alloc I,
        nsw I Y ≤ (Real.exp (1 / Real.exp 1) - c) *
          coinAvg (p.eval (encInst I).length) (fun w => nsw I (decodeAlloc I (A (I, w)))) := by sorry

end NSWBetter
