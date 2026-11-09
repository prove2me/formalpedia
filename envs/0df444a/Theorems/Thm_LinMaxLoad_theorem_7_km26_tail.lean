-- Prove2me | Theorems.Thm_LinMaxLoad_theorem_7_km26_tail
-- name    : LinMaxLoad.theorem_7_km26_tail
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:35:38.554767+00:00
-- url     : https://prove2.me/theorems/344a61de-30e8-4a20-ab6c-9614e800e4f1
-- title:
--   Proof of Theorem 7 — the [KM26] tail bound $\Pr[M(S,h)\ge T] \le \frac{9m}{nT}e^{24q\ell/T} \le \frac{9}{Te^{L/2}}$
-- statement:
--   Let $K$ be a finite field with $q$ elements, $E$ a finite $K$-vector space with $\dim E \ge \ell \ge 1$, $n := q^\ell$, $h : E \to K^\ell$ a uniformly random linear map, and $S \subseteq E$ a set of size $m < n$. Let
--
--   $$
--   L = \log(n/m), \qquad T_0 = 8q + \frac{48 q \ell}{L}.
--   $$
--
--   Then for every integer $T$ with $T_0 \le T \le m$,
--
--   $$
--   \Pr\big[M(S, h) \ge T\big] \le \frac{9m}{nT} \exp\Big(\frac{24 q\ell}{T}\Big) \le \frac{9 m e^{L/2}}{nT} = \frac{9}{T e^{L/2}} .
--   $$
--
--   The first inequality is the paper's application of Corollary 3.4 of [KM26] (Kumar–Mon, tail bounds for the max load of random linear maps over $\mathbb F_q$); the other two are the computation that follows. Summing this tail over $T_0 \le T \le m$ gives Theorem 7.
--
--   **Formalization Note** $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - generalization: $\mathbb F_q^u$ with $u \ge \ell$ → any finite vector space $E$ over any finite field $K$ ($q = |K|$) with $\dim E \ge \ell$; reason: every such $E$ is isomorphic to $K^{\dim E}$ and every finite field has prime-power order, so $E = \mathbb F_q^u$ is the source statement
--   - encoding: $T_0 \le T \le m$ (the tail is summed over integers $T$) → $T \in \mathbb N$; reason: for real $T$ the left side equals its value at $\lceil T\rceil \le m$ and the right sides decrease in $T$, so the integer case gives the real one
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), proof of Theorem 7, KM26 tail display, p.8

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_probLin

namespace LinMaxLoad

open Classical in
/-- **Proof of Theorem 7, the \[KM26\] tail bound** (p.8 of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `q = |K|`, `1 ≤ ℓ ≤ dim E`, `n := q^ℓ`, `h : E → K^ℓ` a uniformly random linear map and
`S ⊆ E` of size `m < n`. Let `L = log(n/m)` and `T₀ = 8q + 48qℓ/L`. For every integer `T` with
`T₀ ≤ T ≤ m`,
`Pr[M(S, h) ≥ T] ≤ (9m/(nT)) exp(24qℓ/T) ≤ 9m e^{L/2}/(nT) = 9/(T e^{L/2})`.

**Formalization Note** The first inequality is the page's application of Corollary 3.4 of
\[KM26\] (Kumar–Mon); it is stated exactly as the page uses it. `log` is the natural logarithm.
`E = F_q^u` with `u ≥ ℓ` on the page; here `E` is any finite `K`-module with `dim E ≥ ℓ`. -/
theorem theorem_7_km26_tail {K E : Type*} [Field K] [Fintype K] [AddCommGroup E]
    [Module K E] [Finite E] (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓE : ℓ ≤ Module.finrank K E)
    (S : Finset E) (hSn : S.card < Fintype.card K ^ ℓ) (T : ℕ)
    (hT₀ : 8 * (Fintype.card K : ℝ) + 48 * (Fintype.card K : ℝ) * ℓ /
        Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) ≤ T)
    (hTm : T ≤ S.card) :
    probLin K E ℓ (fun h => T ≤ maxLoad (h : E → Fin ℓ → K) S) ≤
        9 * (S.card : ℝ) / ((Fintype.card K : ℝ) ^ ℓ * T) *
          Real.exp (24 * (Fintype.card K : ℝ) * ℓ / T) ∧
      9 * (S.card : ℝ) / ((Fintype.card K : ℝ) ^ ℓ * T) *
          Real.exp (24 * (Fintype.card K : ℝ) * ℓ / T) ≤
        9 * (S.card : ℝ) * Real.exp (Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) / 2) /
          ((Fintype.card K : ℝ) ^ ℓ * T) ∧
      9 * (S.card : ℝ) * Real.exp (Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) / 2) /
          ((Fintype.card K : ℝ) ^ ℓ * T) =
        9 / (T * Real.exp (Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) / 2)) := by sorry

end LinMaxLoad
