-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_lemma_4_7
-- name    : MeanCertificates1424.Hardness.Supplement.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:04:09.992889+00:00
-- url     : https://prove2.me/theorems/9838bd95-ec84-4561-896f-48dabb7f5511
-- title:
--   Lemma 4.7 — counter composition
-- statement:
--   Let $h=n-b$ and $\kappa=\min\{b,h\}$. For $W\subseteq V$ and a labeling, $\mathrm{mis}_W$ counts the mismatched vertices of $W$. If $b\le h$ the counter is $\chi_W=\mathrm{mis}_W$, kept only while at most $b$, with $i\oplus j=i+j$ defined when $i+j\le b$, and every defined final value is accepted. If $h<b$ the counter is $\chi_W=\min\{h,|W|-\mathrm{mis}_W\}$ with $i\oplus j=\min\{h,i+j\}$, and only the final value $h$ is accepted. Then for disjoint $W_1,W_2$,
--   $$\chi_{W_1\cup W_2}=\chi_{W_1}\oplus\chi_{W_2},$$
--   every defined value lies in $\{0,\dots,\min\{\kappa,|W_1\cup W_2|\}\}$, and a labeling of $V$ has at most $b$ mismatches iff its counter is defined and accepted.
--
--   The counters carry the single global budget through the dynamic programs.
--
--   Differences from the source:
--   - encoding: a labeling x with mismatches |x_v − y_v| > ε → an arbitrary mismatch predicate on V; reason: every predicate is the mismatch set of some labeling, and the counters depend only on it
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Lemma 4.7, printed p.15 (PDF p.17); counters defined in §4.2, printed p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Lemma 4.7, printed p.15 / PDF p.17. For disjoint `W₁, W₂`, `χ_{W₁∪W₂} = χ_{W₁} ⊕ χ_{W₂}`
and every defined counter value lies in `{0, …, min{κ, |W₁ ∪ W₂|}}` (`κ = min{b, n − b}`);
a labeling has at most `b` mismatches iff its counter on `V` is defined and accepted.
`mis v` is the mismatch indicator `|x_v − y_v| > ε` of the labeling. -/
theorem lemma_4_7 (n b : ℕ) (hb : b ≤ n) (mis : Fin n → Prop) :
    (∀ W₁ W₂ : Finset (Fin n), Disjoint W₁ W₂ →
      counter n b mis (W₁ ∪ W₂) = combine n b (counter n b mis W₁) (counter n b mis W₂) ∧
      ∀ c, counter n b mis (W₁ ∪ W₂) = some c → c ≤ min (min b (n - b)) (W₁ ∪ W₂).card) ∧
    (Accepted n b (counter n b mis Finset.univ) ↔ misCount mis Finset.univ ≤ b) := by sorry

end MeanCertificates1424.Hardness.Supplement
