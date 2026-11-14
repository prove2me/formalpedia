-- Prove2me | Theorems.Thm_LinearChoresCLS_lemma_6_3
-- name    : LinearChoresCLS.lemma_6_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T21:50:26.161006+00:00
-- url     : https://prove2.me/theorems/df2c601c-e526-4012-b87f-88c3c8e3887f
-- title:
--   Lemma 6.3 — output prices and optimal ratios of a Maximum–Minimum gadget
-- statement:
--   Consider a valid chores market containing a Maximum–Minimum gadget on chores $(j,j')$: agents $a^{\max},a^{(1)},a^{(2)}$ with common earning requirement $B$, output chores $p^+,p^-$ with common supply $S$, and designated disutilities $d(a^{\max},j)=d(a^{\max},j')=q$, $d(a^{\max},p^+)=1$, $d(a^{(1)},j)=1/q$, $d(a^{(1)},p^-)=1$, $d(a^{(2)},j')=1/q$, $d(a^{(2)},p^-)=1$. Let $(p,z)$ be an equilibrium such that
--
--   1. the three gadget agents use only their designated chores, and
--   2. the price condition holds: $\sum_{a\in N^+_{\mathrm{out}}}B_a<Sp^+<B$ and $\sum_{a\in N^-_{\mathrm{out}}}B_a<Sp^-<B$, where $N^\pm_{\mathrm{out}}$ are the agents outside the gadget that use $p^\pm$.
--
--   Then
--   $$
--   p^+=\frac{\max\{p_j,p_{j'}\}}{q},\quad p^-=q\min\{p_j,p_{j'}\},\quad \log\frac{p^+}{p^-}=|\Delta_{(j,j'),0}|-2\log q,
--   $$
--   with $\Delta_{(j,j'),0}=\log(p_j/p_{j'})$, and the optimal ratios are $\mu_{a^{\max}}(p)=\max\{p_j,p_{j'}\}/q$, $\mu_{a^{(1)}}(p)=qp_j$, $\mu_{a^{(2)}}(p)=qp_{j'}$.
--
--   The gadget produces a price proportional to a maximum, whose logarithm contains the absolute-value term $\frac12|\Delta|$.
--
--   **Formalization Note** The gadget's agents and chores are distinct; "uses" is $z_{a\ell}>0$; the remaining entries of the market (the dashes of Definition 6.1) are arbitrary positive numbers.
--
--   Differences from the source:
--   - generalization: gadget parameter q > 1 (Figure 3) → any q allowed by the market's validity (q > 0); reason: the proof (p.20) does not use q > 1; q > 1 is a special case
--   - encoding: the gadget adds three new agents and two new chores → explicit distinctness hypotheses on the five chores and three agents; reason: Lean has no notion of "new"; distinctness is what newness means
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Lemma 6.3, Eqs. (6.7)–(6.8), p.20 (Definition 6.1, pp.18–19)

import Mathlib
import Definitions.Def_LinearChoresCLS_Psi

open Finset

namespace LinearChoresCLS

open Classical in
/-- **Lemma 6.3** (arXiv:2611.06589, held version sha256 85d34a9e…, p.20). Consider a market
containing a Maximum-Minimum gadget on chores `(j, j′)` (Definition 6.1, p.18–19): agents
`a^max, a^{(1)}, a^{(2)}` with the same earning requirement `B`, output chores `p^+, p^−` with the
same supply `S`, and designated disutilities `d(a^max, j) = d(a^max, j′) = q`, `d(a^max, p^+) = 1`,
`d(a^{(1)}, j) = 1/q`, `d(a^{(1)}, p^−) = 1`, `d(a^{(2)}, j′) = 1/q`, `d(a^{(2)}, p^−) = 1`. Suppose at
the equilibrium `(p, z)` (1) the three gadget agents use only their designated chores and
(2) the price condition holds: `∑_{a ∈ N^+_out} B_a < S p^+ < B` and
`∑_{a ∈ N^−_out} B_a < S p^− < B`, where `N^±_out` are the agents outside the gadget using `p^±`.
Then `p^+ = max{p_j, p_{j′}}/q`, `p^− = q min{p_j, p_{j′}}`,
`log(p^+/p^−) = |Δ_{(j,j′),0}| − 2 log q` with `Δ_{(j,j′),0} = log(p_j/p_{j′})` (6.7), and
`μ_{a^max}(p) = max{p_j, p_{j′}}/q`, `μ_{a^{(1)}}(p) = q p_j`, `μ_{a^{(2)}}(p) = q p_{j′}` (6.8).

**Formalization Note.** The market is any valid market; the dashes of Definition 6.1 are its
remaining (arbitrary positive) disutilities. `q` is any value the market's validity allows
(`q > 0`), not only `q > 1` as in Figure 3. "Uses" is `z_{aℓ} > 0`. -/
theorem lemma_6_3 {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
    (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ) (z : N → M → ℝ) (hCE : F.IsCE p z)
    (j j' pplus pminus : M) (hjj' : j ≠ j') (hpj : pplus ≠ j) (hpj' : pplus ≠ j')
    (hmj : pminus ≠ j) (hmj' : pminus ≠ j') (hpm : pplus ≠ pminus)
    (amax a1 a2 : N) (h01 : amax ≠ a1) (h02 : amax ≠ a2) (h12 : a1 ≠ a2) (B S q : ℝ)
    (hB : F.earn amax = B ∧ F.earn a1 = B ∧ F.earn a2 = B)
    (hS : F.supply pplus = S ∧ F.supply pminus = S)
    (hd : F.disutil amax j = q ∧ F.disutil amax j' = q ∧ F.disutil amax pplus = 1 ∧
      F.disutil a1 j = 1 / q ∧ F.disutil a1 pminus = 1 ∧
      F.disutil a2 j' = 1 / q ∧ F.disutil a2 pminus = 1)
    (hdes : (∀ ℓ, 0 < z amax ℓ → ℓ = j ∨ ℓ = j' ∨ ℓ = pplus) ∧
      (∀ ℓ, 0 < z a1 ℓ → ℓ = j ∨ ℓ = pminus) ∧ (∀ ℓ, 0 < z a2 ℓ → ℓ = j' ∨ ℓ = pminus))
    (hpc : (∑ a ∈ univ.filter (fun a => a ≠ amax ∧ a ≠ a1 ∧ a ≠ a2 ∧ 0 < z a pplus), F.earn a)
        < S * p pplus ∧ S * p pplus < B ∧
      (∑ a ∈ univ.filter (fun a => a ≠ amax ∧ a ≠ a1 ∧ a ≠ a2 ∧ 0 < z a pminus), F.earn a)
        < S * p pminus ∧ S * p pminus < B) :
    p pplus = max (p j) (p j') / q ∧ p pminus = q * min (p j) (p j') ∧
      Real.log (p pplus / p pminus) = |Real.log (p j / p j')| - 2 * Real.log q ∧
      F.mu amax p = max (p j) (p j') / q ∧ F.mu a1 p = q * p j ∧ F.mu a2 p = q * p j' := by sorry

end LinearChoresCLS
