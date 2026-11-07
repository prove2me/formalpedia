-- Prove2me | Theorems.Thm_KTCenter_lemma_4_5
-- name    : KTCenter.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:44.331032+00:00
-- url     : https://prove2.me/theorems/b6bc655d-009d-41c5-93a6-8957fefb6d84
-- title:
--   Lemma 4.5 — at most $4h$ candidates on the wrong side of $v$
-- statement:
--   Let $T$ be a tournament and $v$ a candidate. Partition the other candidates into disjoint sets $L,R,H$ with $h=|H|$, and suppose $T$ contains $\ell\to v$ for every $\ell\in L$, $v\to r$ for every $r\in R$, and $\ell\to r$ for every $(\ell,r)\in L\times R$. Then in every ranking $\omega$ minimizing $c_T$,
--
--   $$|\{r\in R:r\prec_\omega v\}|\le4h\qquad\text{and}\qquad|\{\ell\in L:v\prec_\omega\ell\}|\le4h.$$
--
--   This is the step that turns the tournament's prescribed comparisons into movement bounds.
--
--   Differences from the source: none.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 4.5, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_KTCenter_Tournament

namespace KTCenter

/-- **Lemma 4.5** (Ordering around a candidate with prescribed comparisons), p.20 (PDF p.22).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** For an arbitrary tournament, as printed. `L`, `R`, `H` partition the
candidates other than `v`. -/
theorem lemma_4_5 {d : ℕ} (T : Tournament d) (v : Fin d) (L R H : Finset (Fin d))
    (hLR : Disjoint L R) (hLH : Disjoint L H) (hRH : Disjoint R H)
    (hcover : L ∪ R ∪ H = Finset.univ.erase v)
    (hL : ∀ l ∈ L, T.arc l v = true) (hR : ∀ r ∈ R, T.arc v r = true)
    (hLRarc : ∀ l ∈ L, ∀ r ∈ R, T.arc l r = true)
    (ω : Equiv.Perm (Fin d)) (hω : ∀ ω', T.cost ω ≤ T.cost ω') :
    (R.filter fun r => ω⁻¹ r < ω⁻¹ v).card ≤ 4 * H.card ∧
      (L.filter fun l => ω⁻¹ v < ω⁻¹ l).card ≤ 4 * H.card := by sorry

end KTCenter
