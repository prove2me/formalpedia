-- Prove2me | Theorems.Thm_LipStableCA_lemma_4_8
-- name    : LipStableCA.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:26.328976+00:00
-- url     : https://prove2.me/theorems/dd6ae3b7-fc38-4b4b-83c0-9a47bc99fb62
-- title:
--   Lemma 4.8 — the selected index changes with probability at most $mR^{1/m}\delta_i/\epsilon$
-- statement:
--   Fix a bidder $i$ and profiles $v,w$ with $v_{-i}=w_{-i}$ and $\delta_i(v,w)<\infty$, so $v_i$ and $w_i$ have the same zero pattern $\mathcal B$, of size $R$. For the discounts of Mechanism 2,
--   $$\Pr\bigl[J(v,a)\ne J(w,a)\bigr]\le\frac{m\,R^{1/m}}{\epsilon}\,\delta_i(v,w).$$
--
--   Since $R\le 2^m-1$, the factor $R^{1/m}$ is at most $2$. This is where the $m$-th root discount distribution pays off.
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: a total order on $\mathcal A$ fixed before the reports are seen → an explicit `LinearOrder` parameter, for every order; reason: Lean convention; same instances
--   - encoding: Pr over the seed of Mechanism 2 → the law `discountMeasure` of the independent uniforms $U_{i,B}$; reason: the discounts are functions of $U$; the coins do not enter these events
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 4.8, p.16

import Definitions.Def_LipStableCA_discountIndex
import Definitions.Def_LipStableCA_profileDist

namespace LipStableCA

/-- **Lemma 4.8.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.16. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. an explicit `LinearOrder` parameter, for every order: Lean convention; same instances. the law `discountMeasure` of the independent uniforms `U_{i,B}`: the discounts are functions of `U`; the coins do not enter these events. -/
theorem lemma_4_8 {n m : ℕ} (hm : 1 ≤ m) (ord : LinearOrder (Alloc n m)) {ϵ : ℝ} (h0 : 0 < ϵ)
    (h1 : ϵ < 1) (i : Fin n) (v w : Profile n m) (hv : IsProfile v) (hw : IsProfile w)
    (hsame : ∀ h, h ≠ i → v h = w h) (hδ : deltaI v w i ≠ ⊤) :
    (discountMeasure n m).real
        {U | selectedIndex ord i (positiveBundles (v i)) (discount ϵ U) v ≠
          selectedIndex ord i (positiveBundles (v i)) (discount ϵ U) w} ≤
      (m : ℝ) * ((positiveBundles (v i)).card : ℝ) ^ (1 / (m : ℝ)) / ϵ * (deltaI v w i).toReal := by sorry

end LipStableCA
