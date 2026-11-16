-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_lemma_4_3
-- name    : MeanCertificates1424.Hardness.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:02:19.459201+00:00
-- url     : https://prove2.me/theorems/6037af49-6499-4c26-b135-0520c2acd2b3
-- title:
--   Lemma 4.3 — deletion-stable truncated alphabets
-- statement:
--   Give the $n$ report anchors and the $|Q|$ audit anchors distinct source identities (two when a vertex is reported and audited), ordered by a fixed injective identity order. At a vertex $v$ order the source values $y_i+\epsilon+Ld_G(i,v)$ and $\beta_a+Ld_G(a,v)$ increasingly, ties broken by identity, and let $A^+_{v,b}$ be the set of numerical values of the first $b+1$ sources; $A^-_{v,b}$ applies the construction to $-y$ and the reflected audit intervals $[-\beta_q,-\alpha_q]$ and negates the values. In an anchored instance:
--
--   1. there are at least $b+1$ sources, so the first $b+1$ sources at every vertex are defined (for the upper and the reflected construction), and both lists have at most $b+1$ values;
--   2. for every honest set $H$ with $|H|=n-b$ and $P_H\ne\emptyset$, the upper envelope lies in $\prod_vA^+_{v,b}$ and the lower envelope in $\prod_vA^-_{v,b}$;
--   3. both truncated alphabets preserve the aggregate optima: if $C_I(y)\ne\emptyset$, some feasible field with values in $A^+_{v,b}$ has mean $u_I(y)$ and some feasible field with values in $A^-_{v,b}$ has mean $\ell_I(y)$.
--
--   Ranks are taken over identities; duplicate values are removed only after truncation.
--
--   Differences from the source:
--   - reading: a fixed global order on identities → every injective identity order; reason: the lemma holds for any fixed order, which is the source's quantifier
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Lemma 4.3, printed p.13 (PDF p.15)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Lemma 4.3, printed p.13 / PDF p.15. With distinct source identities ordered by any fixed
injective `ord`, in an anchored instance there are at least `b + 1` sources, the first `b + 1`
sources at every vertex are defined (exactly `b + 1` of them, for the upper and for the
reflected construction), both truncated alphabets have at most `b + 1` values, the upper
envelope of every feasible component `P_H` (`|H| = n − b`) lies in `∏_v A⁺_{v,b}` and its lower
envelope in `∏_v A⁻_{v,b}`, and both truncated alphabets preserve the aggregate optima. -/
theorem lemma_4_3 (I : Inst) (hI : Valid I) (hA : Anchored I) (ord : Source I.n → ℕ)
    (hord : Function.Injective ord) :
    I.budget + 1 ≤ (sources I).card ∧
    (∀ v, (topSources (sources I) (fun a => srcHi I a + I.lip * gdist I (srcLoc a) v) ord
          (I.budget + 1)).card = I.budget + 1 ∧
      (topSources (sources (reflect I))
          (fun a => srcHi (reflect I) a + I.lip * gdist I (srcLoc a) v) ord
          (I.budget + 1)).card = I.budget + 1 ∧
      (truncUp I ord v).card ≤ I.budget + 1 ∧ (truncLow I ord v).card ≤ I.budget + 1) ∧
    (∀ H : Finset (Fin I.n), H.card = I.n - I.budget → (PH I H).Nonempty →
      ∀ v, UH I H v ∈ truncUp I ord v ∧ LH I H v ∈ truncLow I ord v) ∧
    ((CI I).Nonempty →
      (∃ x ∈ CI I, (∀ v, x v ∈ truncUp I ord v) ∧ (wmean I x : EReal) = upper I) ∧
      (∃ x ∈ CI I, (∀ v, x v ∈ truncLow I ord v) ∧ (wmean I x : EReal) = lower I)) := by sorry

end MeanCertificates1424.Hardness.Supplement
