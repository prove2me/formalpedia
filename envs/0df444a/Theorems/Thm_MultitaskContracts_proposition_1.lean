-- Prove2me | Theorems.Thm_MultitaskContracts_proposition_1
-- name    : MultitaskContracts.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:33:43.453409+00:00
-- url     : https://prove2.me/theorems/91455897-34eb-483a-8cdb-2f3db4eec0f3
-- title:
--   Proposition 1 (Laux) — identical independent tasks: the optimal AoN contract pays $|K|c/(p^{|K|}-q^{|K|})$ and $\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}=|K|c/(1-(q/p)^{|K|})$
-- statement:
--   Let $I$ be an instance with identical independent tasks, sharing the cost $c$ and the success probabilities $p>q\ge0$ ($c,p,q$ are the values at any task $k_0$), and let $n=|K|$. Then
--   1. $\dfrac{c(K)}{P_K(K)-P_\emptyset(K)}=\dfrac{nc}{p^n-q^n}$;
--   2. the AoN contract paying $t(K)=\dfrac{nc}{p^n-q^n}$ (and $0$ on every $Y\subsetneq K$) implements full effort, and its expected payment equals $\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}$;
--   3. an AoN contract implements full effort with expected payment $\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}$ if and only if it pays exactly $t(K)=\dfrac{nc}{p^n-q^n}$;
--   4. $$\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}=\frac{nc}{1-(q/p)^n}.$$
--
--   This closed form gives the denominator of the lower-bound instances in Theorem 2.
--
--   Differences from the source:
--   - reading: "the optimal Min-Pay contract is AoN and pays t(K)" → the AoN contract paying t(K) is optimal, and an AoN contract is optimal iff it pays t(K); reason: read literally ("every optimal contract is AoN") the claim is false — two independent identical tasks with p = 1, q = 0, c = 1: t(K) = 2, t({1}) = 1, t = 0 elsewhere implements K at expected payment 2 = OPT and is not AoN; the proof sketch says "some optimal contract is AoN"
--   - encoding: the common c, p, q → the values c_{k₀}, p_{k₀}, q_{k₀} at an arbitrary task k₀; reason: identical tasks share them, and k₀ exists since K ≠ ∅ in the source's formula
--   - encoding: OPT^Bun_MinPay → ℝ≥0∞ value; reason: same value (finite here)
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Proposition 1 (Laux [Lau01]), §4.1.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_IsAoN
import Definitions.Def_MultitaskContracts_Instance_IsIndependent
import Definitions.Def_MultitaskContracts_Instance_IsIdentical

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Proposition 1** (Laux [Lau01]; §4.1.1, p.13, PDF 15). For identical independent tasks with
common `c, p, q` (the values at any task `k₀`), writing `n = |K|`:
1. `c(K)/(P_K(K) − P_∅(K)) = n c/(pⁿ − qⁿ)`;
2. the AoN contract paying `t(K) = n c/(pⁿ − qⁿ)` implements full effort and its expected payment
   is `OPT^Bun_MinPay`;
3. an AoN contract implements full effort at expected payment `OPT^Bun_MinPay` if and only if it
   pays exactly `t(K) = n c/(pⁿ − qⁿ)`;
4. `OPT^Bun_MinPay = n c/(1 − (q/p)ⁿ)`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Proposition 1, p.13.

**Formalization Note.** Reading of "the optimal Min-Pay contract is AoN and pays t(K)": the
optimal AoN contract is unique and pays `t(K)`, and `OPT^Bun_MinPay` is attained by it. The
literal reading "every optimal contract is AoN" is false (two tasks, `p = 1`, `q = 0`, `c = 1`:
`t(K) = 2`, `t({1}) = 1`, `t = 0` elsewhere is optimal and not AoN). -/
theorem proposition_1 (I : Instance K) (hind : I.IsIndependent) (hid : I.IsIdentical) (k₀ : K) :
    I.cost Finset.univ / (I.P Finset.univ Finset.univ - I.P ∅ Finset.univ) =
        (Fintype.card K : ℝ) * I.c k₀ / (I.p k₀ ^ Fintype.card K - I.q k₀ ^ Fintype.card K) ∧
    (I.Implements
        (fun Y => if Y = Finset.univ then
          (Fintype.card K : ℝ) * I.c k₀ / (I.p k₀ ^ Fintype.card K - I.q k₀ ^ Fintype.card K)
          else 0) Finset.univ ∧
      ENNReal.ofReal (I.expect Finset.univ
        (fun Y => if Y = Finset.univ then
          (Fintype.card K : ℝ) * I.c k₀ / (I.p k₀ ^ Fintype.card K - I.q k₀ ^ Fintype.card K)
          else 0)) = I.optMinPay (bundle K)) ∧
    (∀ t : Finset K → ℝ, IsAoN t →
      ((I.Implements t Finset.univ ∧
          ENNReal.ofReal (I.expect Finset.univ t) = I.optMinPay (bundle K)) ↔
        t Finset.univ =
          (Fintype.card K : ℝ) * I.c k₀ / (I.p k₀ ^ Fintype.card K - I.q k₀ ^ Fintype.card K))) ∧
    I.optMinPay (bundle K) =
      ENNReal.ofReal ((Fintype.card K : ℝ) * I.c k₀ / (1 - (I.q k₀ / I.p k₀) ^ Fintype.card K)) := by sorry

end MultitaskContracts
