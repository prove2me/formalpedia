-- Prove2me | Theorems.Thm_MultitaskContracts_theorem_2_identical_ratio
-- name    : MultitaskContracts.theorem_2_identical_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:34:04.388951+00:00
-- url     : https://prove2.me/theorems/e4420a44-87ce-4c53-8712-73c3fe041609
-- title:
--   Proof of Theorem 2, lower bound — identical tasks: $\mathrm{OPT}^{\mathrm{Sep}}/\mathrm{OPT}^{\mathrm{Bun}}=\sum_{\ell<|K|}(q/p)^\ell\ge|K|(q/p)^{|K|-1}$
-- statement:
--   Let $I$ be an instance with identical independent tasks, sharing $c$ and $p>q\ge0$ (the values at any task $k_0$); write $n=|K|$ and $r=q/p$. Then
--   1. $\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinPay}}=\dfrac{nc}{1-r}$;
--   2. $$\frac{\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinPay}}}{\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}}=\frac{1-r^n}{1-r}=\sum_{\ell=0}^{n-1}r^\ell\ \ge\ n\,r^{\,n-1};$$
--   3. if moreover $n\ge2$, $\varepsilon\in(0,1)$, $p=1$ and $q=(1-\varepsilon)^{1/(n-1)}$, then $n\,r^{\,n-1}=(1-\varepsilon)\,n$.
--
--   As $\varepsilon$ is arbitrary, the ratio comes arbitrarily close to $|K|$, which gives the lower bound of Theorem 2.
--
--   Differences from the source:
--   - generalization: the display for the instance p = 1, q = (1 − ε)^{1/(|K|−1)} → the identities and the inequality for every identical independent instance (any common 0 ≤ q < p ≤ 1), plus clause 3 for the paper's choice; reason: specializing to p = 1, q = (1 − ε)^{1/(|K|−1)} gives the paper's display, including its last equality
--   - encoding: the ratio OPT^Sep/OPT^Bun → sepRatio of the two ℝ≥0∞ optima (Definition 1's ratio); reason: both optima are finite and positive, so it is the ordinary ratio
--   - encoding: the common c, p, q of the identical tasks → the values c_{k₀}, p_{k₀}, q_{k₀} at an arbitrary task k₀; reason: identical tasks share them, and k₀ exists since the display needs |K| ≥ 1
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), proof of Theorem 2, lower bound, display "OPT^Sep_MinPay/OPT^Bun_MinPay = (1 − (q/p)^{|K|})/(1 − q/p) = …", p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_separable
import Definitions.Def_MultitaskContracts_priceOfSeparation
import Definitions.Def_MultitaskContracts_Instance_IsIndependent
import Definitions.Def_MultitaskContracts_Instance_IsIdentical

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Lower-bound display in the proof of Theorem 2** (§4.1.3, p.15, PDF 17). For identical
independent tasks with common `c, p, q` (the values at any task `k₀`), `n = |K|` and `r = q/p`:
`OPT^Sep_MinPay = n c/(1 − r)` and
`OPT^Sep_MinPay / OPT^Bun_MinPay = (1 − rⁿ)/(1 − r) = ∑_{ℓ=0}^{n−1} rˡ ≥ n r^{n−1}`;
and when `p = 1`, `q = (1 − ε)^{1/(n−1)}` with `n ≥ 2`, `ε ∈ (0, 1)`, `n r^{n−1} = (1 − ε) n`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), proof of Theorem 2, p.15.

**Formalization Note.** The display is stated for every common `0 ≤ q < p ≤ 1`, not only the
paper's choice `p = 1`, `q = (1 − ε)^{1/(n−1)}`, which the last clause covers. The ratio is the
`sepRatio` of Definition 1 in `ℝ≥0∞`. -/
theorem theorem_2_identical_ratio (I : Instance K) (hind : I.IsIndependent) (hid : I.IsIdentical)
    (k₀ : K) :
    I.optMinPay (separable K) =
        ENNReal.ofReal ((Fintype.card K : ℝ) * I.c k₀ / (1 - I.q k₀ / I.p k₀)) ∧
    sepRatio (I.optMinPay (separable K)) (I.optMinPay (bundle K)) =
        ENNReal.ofReal ((1 - (I.q k₀ / I.p k₀) ^ Fintype.card K) / (1 - I.q k₀ / I.p k₀)) ∧
    (1 - (I.q k₀ / I.p k₀) ^ Fintype.card K) / (1 - I.q k₀ / I.p k₀) =
        ∑ ℓ ∈ Finset.range (Fintype.card K), (I.q k₀ / I.p k₀) ^ ℓ ∧
    (Fintype.card K : ℝ) * (I.q k₀ / I.p k₀) ^ (Fintype.card K - 1) ≤
        ∑ ℓ ∈ Finset.range (Fintype.card K), (I.q k₀ / I.p k₀) ^ ℓ ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 → 2 ≤ Fintype.card K → I.p k₀ = 1 →
      I.q k₀ = (1 - ε) ^ (1 / ((Fintype.card K : ℝ) - 1)) →
      (Fintype.card K : ℝ) * (I.q k₀ / I.p k₀) ^ (Fintype.card K - 1) =
        (1 - ε) * Fintype.card K := by sorry

end MultitaskContracts
