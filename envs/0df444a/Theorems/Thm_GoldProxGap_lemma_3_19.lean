-- Prove2me | Theorems.Thm_GoldProxGap_lemma_3_19
-- name    : GoldProxGap.lemma_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:21:55.653789+00:00
-- url     : https://prove2.me/theorems/3990db18-aa24-461d-86bc-313b6ce8116f
-- title:
--   Lemma 3.19 — collision averaging: some choice gives $\max\{M-\lfloor F/r\rfloor,\lceil rM^2/(rM+2F)\rceil\}$ distinct values
-- statement:
--   **Lemma 3.19 (Collision averaging).** Suppose $M\ge1$ indexed values are computed for each of $r>0$ parameter choices. If the total number of unordered colliding index pairs, summed over all choices, is at most $F$, some choice gives at least
--   $$
--   \max\Bigl\{M-\lfloor F/r\rfloor,\ \Bigl\lceil\frac{rM^2}{rM+2F}\Bigr\rceil\Bigr\}
--   $$
--   distinct values. At most one of them is zero.
--
--   In the proof of Theorem 5.1 the parameter is the pole $\beta$ and the values are the challenges $z_i=C_i(\beta)$; the lemma keeps many of them distinct.
--
--   **Formalization Note** The parameter choices form a finite type $P$ with $|P|=r>0$, the values are $v_p:\{0,\dots,M-1\}\to\alpha$, an unordered colliding pair at $p$ is a pair $i<j$ with $v_p(i)=v_p(j)$, and $F$ is real. Both lower bounds are stated at the same choice $p$.
--
--   Differences from the source:
--   - encoding: r parameter choices, M indexed values, unordered colliding pairs, a bound F → a finite type P with card P = r > 0, values v : P → Fin M → α, pairs i < j with equal values, a real F; reason: same data
--   - encoding: at least max{a, b} distinct values → both lower bounds a and b at the same choice; reason: ≥ max{a, b} is ≥ a and ≥ b
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 3.19, p.26

import Mathlib

open scoped Classical

namespace GoldProxGap

/-- **Lemma 3.19 (Collision averaging)**, p.26. Dao, Kominers, Thaler, Zheng, *Counterexamples to
Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission manuscript
(2 November 2026, sha256 6c2d9ced…): "Suppose M ≥ 1 indexed values are computed for each of
r > 0 parameter choices. If the total number of unordered colliding index pairs, summed over all
choices, is at most F, some choice gives at least max{M − ⌊F/r⌋, ⌈rM²/(rM + 2F)⌉} distinct
values. At most one of them is zero."

**Formalization Note.** The parameter choices are a finite type `P` with `r = |P| > 0`; the
values are `v p : Fin M → α`. An unordered colliding pair at `p` is a pair of indices `i < j`
with `v p i = v p j`. `F` is a real number. "At least the max" is stated as both lower bounds at
the same choice `p`. The distinct values at `p` are the image `{v p i : i}`. -/
theorem lemma_3_19 {P : Type*} [Fintype P] {α : Type*} [Zero α] (M : ℕ) (hM : 1 ≤ M)
    (hr : 0 < Fintype.card P) (v : P → Fin M → α) (F : ℝ)
    (hF : (∑ p : P, ((Finset.univ.filter
      (fun ij : Fin M × Fin M => ij.1 < ij.2 ∧ v p ij.1 = v p ij.2)).card : ℝ)) ≤ F) :
    ∃ p : P,
      (M : ℝ) - (⌊F / (Fintype.card P : ℝ)⌋ : ℝ) ≤ ((Finset.univ.image (v p)).card : ℝ) ∧
      ⌈((Fintype.card P : ℝ) * (M : ℝ) ^ 2) / ((Fintype.card P : ℝ) * M + 2 * F)⌉ ≤
        ((Finset.univ.image (v p)).card : ℤ) ∧
      ((Finset.univ.image (v p)).filter (fun y => y = 0)).card ≤ 1 := by sorry

end GoldProxGap
