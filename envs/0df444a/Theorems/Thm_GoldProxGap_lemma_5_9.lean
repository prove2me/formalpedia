-- Prove2me | Theorems.Thm_GoldProxGap_lemma_5_9
-- name    : GoldProxGap.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:55.134748+00:00
-- url     : https://prove2.me/theorems/97932f5e-ed0a-4dfb-b1a4-5b71ad5f7ead
-- title:
--   Lemma 5.9 — rank under the moment equations: $\operatorname{rank}A\ge2t$, and at rank $2t$, $J=J_{d-t}L_V^{2^t}$ with $\deg J=N/2^t$
-- statement:
--   **Lemma 5.9 (Rank under the moment equations).** In the setting of (5.2), let $2\le t\le d/2$ and let $A\ne0$ be an alternating binary matrix with $M_1(A)=\dots=M_{t-1}(A)=0$. Then $A$ has rank at least $2t$. If its rank is exactly $2t$ and $V$ is its polar radical, then $|V|=N/2^{2t}$ and
--   $$
--   J=J_{d-t}\,L_V^{2^t},\qquad J_{d-t}\ne0,\qquad \deg J=\frac N{2^t},
--   $$
--   where $J_{d-t}$ is the coefficient of $X^{2^{d-t}}$ in $J$.
--
--   The rank bound shows that the moment equations leave no nonzero solutions of rank below $2t$, which is what the counting of Lemma 5.13 needs.
--
--   **Formalization Note** The polar radical (which depends only on $A$) is that of $\psi_A$, mapped into $\mathbb B$; $L_V$ is its locator. Rank is over $\mathbb F_2$.
--
--   Differences from the source:
--   - encoding: a basis ω₁, …, ω_d of the label space D̂ → a coordinate basis φs of the linear functions D → F₂ with ω_i = label(φs i); reason: by Lemma 5.5(2) the label map is an F₂-linear bijection, so this is the same data
--   - encoding: V is the polar radical, of size N/2^{2t} → V is the polar radical of ψ_A mapped into B, and |V| = N/2^{2t} is a conclusion; reason: the size is a fact the sentence asserts
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 5.9, p.40

import Mathlib
import Definitions.Def_GoldProxGap_quadPoly

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Lemma 5.9 (Rank under the moment equations)**, p.40. Dao, Kominers, Thaler, Zheng,
*Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission
manuscript (2 November 2026, sha256 6c2d9ced…).

"Let 2 ≤ t ≤ d/2, and let A ≠ 0 satisfy M_1(A) = ⋯ = M_{t−1}(A) = 0. Then A has rank at least 2t.
If its rank is exactly 2t, and V is the polar radical, of size N/2^{2t}, then
J = J_{d−t} L_V^{2^t}, J_{d−t} ≠ 0, deg J = N/2^t."

**Formalization Note.** Setting of (5.2) (p.38): `A` alternating binary, a coordinate basis `φs`
of the linear functions with `ω_i = label D (φs i)`. The polar radical `V` (which depends only on
`A`) is that of `ψ_A = psi φs A 0`, mapped into `B`; `L_V` is its locator. The size `N/2^{2t}` of
`V` is stated as a conclusion. `J_{d−t}` is the coefficient of `X^{2^{d−t}}` in `J`. Rank is over
`F₂`. -/
theorem lemma_5_9 {B : Type} [Field B] [Fintype B] [CharP B 2] (D : AddSubgroup B) (d : ℕ)
    (hD : Nat.card D = 2 ^ d) (φs : Fin d → (D →+ ZMod 2)) (hφs : IsCoordBasis D φs)
    (t : ℕ) (ht : 2 ≤ t) (htd : 2 * t ≤ d)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (hA : IsAltBin A) (hA0 : A ≠ 0)
    (hM : ∀ k, 1 ≤ k → k ≤ t - 1 → goldMoment (fun i => label D (φs i)) A k = 0) :
    2 * t ≤ A.rank ∧
    (A.rank = 2 * t →
      let V : Finset B := (polarRadical (psi φs A 0)).map (Function.Embedding.subtype _)
      let J := Jpoly D φs A
      V.card = 2 ^ d / 2 ^ (2 * t) ∧
      J = C (J.coeff (2 ^ (d - t))) * (locator V) ^ (2 ^ t) ∧
      J.coeff (2 ^ (d - t)) ≠ 0 ∧
      J.natDegree = 2 ^ d / 2 ^ t) := by sorry

end GoldProxGap
