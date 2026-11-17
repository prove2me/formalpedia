-- Prove2me | Theorems.Thm_NearLinIsing_Supplement_theorem_6_1
-- name    : NearLinIsing.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:40:31.757124+00:00
-- url     : https://prove2.me/theorems/7f0e2f59-009f-4815-934a-66e877b37a9c
-- title:
--   Theorem 6.1 — Holant criterion for $q\ge3$, (27) and (28) give $h>0$ with $AWh\le h/2$, hence $\lambda_{\max}(AW)\le1/2$
-- statement:
--   Let $H$ be a finite loopless multigraph carrying a Holant model with flow conservation over $\mathbb Z_q$, with $q\ge3$, and put $Q=q-1$. Suppose there are $s\in[1,Q]$ and positive incidence parameters $x_{v,e}$ satisfying
--
--   $$\frac sQ\Big[\prod_{e\ni v}\Big(1+\frac Qs x_{v,e}\Big)-1\Big]\le1\qquad(v\in V(H)),\qquad(27)$$
--
--   and, for every nonempty connected bridgeless support $F$,
--
--   $$Q\,s^{|F|-|V(F)|}\prod_{v\in V(F)}m_v(\delta_F(v))\le\prod_{e=uv\in F}\sqrt{x_{u,e}x_{v,e}}.\qquad(28)$$
--
--   Then there is a positive vector $h$ on the component polymers satisfying
--
--   $$AWh\le h/2,\qquad 1\le h_C\le|V(H)|,\qquad\sum_C w_Ch_C\le|V(H)|/2.$$
--
--   In particular, $\lambda_{\max}(AW)\le1/2$. Equality is allowed in both certificate conditions.
--
--   Here $w_C$ and $A_{CD}=\mathbf 1\{V(F_C)\cap V(F_D)\ne\varnothing\}$ are as in (26), so $(AWh)_C=\sum_D A_{CD}w_Dh_D$, and $m_v(S)=\max_{\operatorname{supp}\zeta=S}f_v(\zeta)/f_v(0)$. Neither condition requires enumerating the polymer space; the criterion feeds the Potts sampler of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: antisymmetric configurations on the directed copies of the edges → labels in one reference direction per edge, the label seen at v being ±ξ_e; reason: the paper's own identification (p. 33)
--   - encoding: positive incidence parameters x_{v,e} → x : V → E → ℝ, positive whenever v is an endpoint of e; reason: (27) and (28) use only these entries
--   - encoding: polymers C = (F_C, ξ^C), positive-weight labelled connected components of the nonzero support → labellings with nonempty connected support and positive weight (26); reason: F_C = supp ξ^C, so the labelling determines the polymer
--   - encoding: s^{|F|−|V(F)|} → an integer power (zpow); reason: same number; no natural-number subtraction
--   - encoding: λmax(AW) ≤ 1/2 → the published Rayleigh-form bound `PolymerModel.LambdaMaxLe (1/2)` for the symmetric realization W^{1/2}AW^{1/2}; reason: §2.4's convention, as in the base mission
--   - encoding: ℤ_q with q ≥ 3 → `ZMod q` with `NeZero q`; reason: implied by q ≥ 3
--   - encoding: signatures f_v : Z_q^{E_v} → ℝ≥0 → `f v : (Inc v → ZMod q) → ℝ` with `f_nonneg`, indexed by the physical edges at v; reason: H is loopless, so E_v is in bijection with δ_H(v); same functions
--   - encoding: m_v(S) = max over ζ with supp ζ = S → `⨆` over the subtype {ζ // localSupp ζ = S}; reason: that index set is finite and nonempty, so the real supremum is the maximum
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Theorem 6.1, pp. 33–34; setting of §6.1 and (26), pp. 32–33

import Mathlib
import Definitions.Def_NearLinIsing_Supplement_Holant

namespace NearLinIsing

namespace Supplement

open Classical

/-- **Theorem 6.1** (Holant criterion for `q ≥ 3`), pp. 33–34.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Theorem 6.1, pp. 33–34 (setting of §6.1, pp. 32–33).

Let `H` be a finite loopless multigraph with a Holant model with flow conservation over `Z_q`,
`q ≥ 3`, and put `Q = q − 1`. Suppose `s ∈ [1, Q]` and positive incidence parameters `x_{v,e}`
satisfy (27) at every vertex `v`,
`(s/Q) [∏_{e ∋ v} (1 + (Q/s) x_{v,e}) − 1] ≤ 1`,
and (28) for every nonempty connected bridgeless support `F`,
`Q s^{|F| − |V(F)|} ∏_{v ∈ V(F)} m_v(δ_F(v)) ≤ ∏_{e = uv ∈ F} √(x_{u,e} x_{v,e})`.
Then there is a vector `h` on the component polymers with `h > 0`, `AWh ≤ h/2`,
`1 ≤ h_C ≤ |V(H)|` and `∑_C w_C h_C ≤ |V(H)|/2`; in particular `λmax(AW) ≤ 1/2`.

**Formalization Note.** `(AWh)_C = ∑_D A_{CD} w_D h_D` with `A_{CD} = 1{C ≁ D}` (diagonal
included); `λmax(AW) ≤ 1/2` is the published `PolymerModel.LambdaMaxLe` (Rayleigh form of
`W^{1/2} A W^{1/2}`). The product in (27) runs over every edge of `H` at `v`, parallel edges
separately; an isolated vertex gives the empty product. `x_{v,e}` is required positive only at
incidences `v ∈ e`, the only entries (27) and (28) use. The exponent `|F| − |V(F)|` is an integer
power (`zpow`). -/
theorem theorem_6_1 {q : ℕ} [NeZero q] (hq : 3 ≤ q) {V E : Type} [Fintype V] [Fintype E]
    (H : Holant q V E) (s : ℝ) (hs1 : 1 ≤ s) (hsQ : s ≤ (q : ℝ) - 1)
    (x : V → E → ℝ) (hx : ∀ v e, H.IsEnd v e → 0 < x v e)
    (h27 : ∀ v : V,
      s / ((q : ℝ) - 1) * ((∏ e : H.Inc v, (1 + ((q : ℝ) - 1) / s * x v e.1)) - 1) ≤ 1)
    (h28 : ∀ F : Finset E, H.IsSupport F →
      ((q : ℝ) - 1) * s ^ ((F.card : ℤ) - ((H.verts F).card : ℤ)) *
          ∏ v ∈ H.verts F, H.mv v (H.incIn F v) ≤
        ∏ e ∈ F, Real.sqrt (x (H.ends e).1 e * x (H.ends e).2 e)) :
    ∃ h : H.Poly → ℝ,
      (∀ C, 0 < h C) ∧
      (∀ C, ∑ D, (if H.polymerModel.compat C D then 0 else 1) * H.polymerModel.w D * h D ≤
        h C / 2) ∧
      (∀ C, 1 ≤ h C ∧ h C ≤ (Fintype.card V : ℝ)) ∧
      ∑ C, H.polymerModel.w C * h C ≤ (Fintype.card V : ℝ) / 2 ∧
      H.polymerModel.LambdaMaxLe (1 / 2) := by sorry

end Supplement

end NearLinIsing
