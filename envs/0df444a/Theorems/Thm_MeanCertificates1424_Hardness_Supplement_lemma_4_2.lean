-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_lemma_4_2
-- name    : MeanCertificates1424.Hardness.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:01:57.030217+00:00
-- url     : https://prove2.me/theorems/a86b84f7-1e09-427a-9fc4-2452af382e33
-- title:
--   Lemma 4.2 — envelopes and common alphabets
-- statement:
--   For a component $P_H$ with at least one anchor let $U^H_v=\min_a\{\beta_a+Ld_G(a,v)\}$ and $\Lambda^H_v=\max_a\{\alpha_a-Ld_G(a,v)\}$.
--
--   1. $P_H\ne\emptyset$ iff $\Lambda^H\le U^H$ pointwise, iff $\alpha_a-\beta_{a'}\le Ld_G(a,a')$ for every pair of anchors.
--   2. In that case $\Lambda^H,U^H\in P_H$, $\Lambda^H\le x\le U^H$ for every $x\in P_H$, and for nonnegative weights the extreme means over $P_H$ are $\mu_w(\Lambda^H)$ and $\mu_w(U^H)$.
--   3. In an anchored instance with $C_I(y)\ne\emptyset$, some maximizer of $\mu_w$ over $C_I(y)$ takes values only in $A^+_v=\{y_i+\epsilon+Ld_G(i,v)\}\cup\{\beta_q+Ld_G(q,v)\}$, and some minimizer only in $A^-_v=\{y_i-\epsilon-Ld_G(i,v)\}\cup\{\alpha_q-Ld_G(q,v)\}$. Each alphabet has at most $n+|Q|\le 2n$ labels.
--
--   The envelopes are the McShane extensions of the anchor data.
--
--   Differences from the source:
--   - reading: (c) If CI(y) is nonempty, some maximizer … → stated for anchored instances; reason: the proof invokes Lemma 4.1, which needs b < n or Q ≠ ∅; an unanchored nonempty class contains all constant fields and has no maximizer
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Lemma 4.2, printed pp.12–13 (PDF pp.14–15)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Lemma 4.2, printed pp.12–13 / PDF pp.14–15. For a component with a nonempty set of
anchors, with `U^H_v = min_a (β_a + L d(a, v))` and `Λ^H_v = max_a (α_a − L d(a, v))`:
(a) `P_H ≠ ∅ ⇔ Λ^H ≤ U^H ⇔ α_a − β_{a'} ≤ L d(a, a')` for all anchors `a, a'`;
(b) then `Λ^H, U^H ∈ P_H`, they bracket every `x ∈ P_H`, and (weights `≥ 0`) the extreme
means over `P_H` are `µ_w(Λ^H)` and `µ_w(U^H)`;
(c) in an anchored instance with `C_I(y) ≠ ∅`, some maximizer of `µ_w` takes values only in
`A⁺_v` and some minimizer only in `A⁻_v`; each alphabet has at most `n + |Q| ≤ 2n` labels. -/
theorem lemma_4_2 (I : Inst) (hI : Valid I) :
    (∀ H : Finset (Fin I.n), (anchorsOf I H).Nonempty →
      ((PH I H).Nonempty ↔ ∀ v, LH I H v ≤ UH I H v) ∧
      ((∀ v, LH I H v ≤ UH I H v) ↔ ∀ a ∈ anchorsOf I H, ∀ a' ∈ anchorsOf I H,
        srcLo I a - srcHi I a' ≤ I.lip * gdist I (srcLoc a) (srcLoc a')) ∧
      ((PH I H).Nonempty →
        LH I H ∈ PH I H ∧ UH I H ∈ PH I H ∧
        (∀ x ∈ PH I H, ∀ v, LH I H v ≤ x v ∧ x v ≤ UH I H v) ∧
        IsGreatest (wmean I '' PH I H) (wmean I (UH I H)) ∧
        IsLeast (wmean I '' PH I H) (wmean I (LH I H)))) ∧
    (Anchored I → (CI I).Nonempty →
      (∃ x ∈ CI I, (∀ x' ∈ CI I, wmean I x' ≤ wmean I x) ∧ ∀ v, x v ∈ fullUp I v) ∧
      (∃ x ∈ CI I, (∀ x' ∈ CI I, wmean I x ≤ wmean I x') ∧ ∀ v, x v ∈ fullLow I v)) ∧
    (∀ v, (fullUp I v).card ≤ I.n + I.audits.card ∧ (fullLow I v).card ≤ I.n + I.audits.card) ∧
    I.n + I.audits.card ≤ 2 * I.n := by sorry

end MeanCertificates1424.Hardness.Supplement
