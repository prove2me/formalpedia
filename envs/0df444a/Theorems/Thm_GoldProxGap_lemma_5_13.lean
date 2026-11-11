-- Prove2me | Theorems.Thm_GoldProxGap_lemma_5_13
-- name    : GoldProxGap.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:25:05.773362+00:00
-- url     : https://prove2.me/theorems/1f421d2f-8983-4bd4-b6e6-2b92b8bab5a9
-- title:
--   Lemma 5.13 — rank-$2t$ solutions of the moment equations: $|\mathcal C_{2t}|\ge[n\ t]_4(2^\Delta-1)$
-- statement:
--   **Lemma 5.13 (Rank-$2t$ solutions of the moment equations).** Let $D\subseteq\mathbb F_{2^m}$ be binary additive of dimension $d$, let $\omega_1,\dots,\omega_d$ be a basis of its label space, and let $2\le t\le n=\lfloor d/2\rfloor$, with $\iota$ ($=1$ for even $d$, $0$ for odd $d$) and $\Delta=m-t(m-d+\iota)\ge1$ as in Theorem 5.1. Let $\mathcal C$ be the space of alternating binary $d\times d$ matrices $A$ with $M_1(A)=\dots=M_{t-1}(A)=0$, and $\mathcal C_{2t}$ the set of its matrices of rank $2t$. Then
--   $$
--   |\mathcal C_{2t}|\ \ge\ \begin{bmatrix}n\\ t\end{bmatrix}_4\,(2^\Delta-1).
--   $$
--
--   This lower bound on the number of admissible matrices is the factor $(2^\Delta-1)[n\ t]_4$ of the list size $L$ in Theorem 5.1.
--
--   **Formalization Note** Rank is over $\mathbb F_2$; $2^\Delta$ is a real power of an integer exponent; $[n\ t]_4$ is `gaussBinom 4 n t`.
--
--   Differences from the source:
--   - encoding: B = F_{2^m} → every field B with 2^m elements; reason: finite fields of the same size are isomorphic
--   - encoding: a basis ω₁, …, ω_d of the label space D̂ → a coordinate basis φs of the linear functions D → F₂ with ω_i = label(φs i); reason: by Lemma 5.5(2) the label map is an F₂-linear bijection, so this is the same data
--   - encoding: B of characteristic two → the instance [CharP B 2] in addition to |B| = 2^m; reason: it follows from |B| = 2^m and is needed to define labels
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 5.13, p.42

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_GoldProxGap_quadPoly

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Lemma 5.13 (Rank-2t solutions of the moment equations)**, p.42. Dao, Kominers, Thaler,
Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027
submission manuscript (2 November 2026, sha256 6c2d9ced…).

"Let D ⊆ F_{2^m} be binary additive of dimension d, let ω₁, …, ω_d be a basis of its label space,
and let 2 ≤ t ≤ n = ⌊d/2⌋, with ι and Δ ≥ 1 as in Theorem 5.1. Let C be the space of alternating
binary d × d matrices A with M_1(A) = ⋯ = M_{t−1}(A) = 0, and let C_{2r} be the set of its matrices
of rank 2r. Then |C_{2t}| ≥ [n t]₄ (2^Δ − 1). (5.6)"

Theorem 5.1 (p.34): "ι = 1 for even d and ι = 0 for odd d, … Δ = m − t(m − d + ι) ≥ 1".

**Formalization Note.** `F_{2^m}` is any field `B` with `2^m` elements (`[CharP B 2]` is stated;
it follows from the cardinality). The basis of the label space is a coordinate basis `φs`,
`ω_i = label D (φs i)`. `Δ` is an integer and `2^Δ` a real power. `[n t]₄` is
`HScattered.Hyperplanes.gaussBinom 4 n t`. Rank is over `F₂`. -/
theorem lemma_5_13 {B : Type} [Field B] [Fintype B] [CharP B 2] (m : ℕ)
    (hB : Fintype.card B = 2 ^ m) (D : AddSubgroup B) (d : ℕ) (hD : Nat.card D = 2 ^ d)
    (φs : Fin d → (D →+ ZMod 2)) (hφs : IsCoordBasis D φs) (t : ℕ) (ht : 2 ≤ t)
    (htn : t ≤ d / 2)
    (hΔ : 1 ≤ (m : ℤ) - (t : ℤ) * ((m : ℤ) - (d : ℤ) + (if Even d then 1 else 0))) :
    let ω : Fin d → B := fun i => label D (φs i)
    let Δ : ℤ := (m : ℤ) - (t : ℤ) * ((m : ℤ) - (d : ℤ) + (if Even d then 1 else 0))
    HScattered.Hyperplanes.gaussBinom 4 (d / 2) t * ((2 : ℝ) ^ Δ - 1) ≤
      ((Finset.univ.filter (fun A : Matrix (Fin d) (Fin d) (ZMod 2) =>
        IsAltBin A ∧ (∀ k, 1 ≤ k → k ≤ t - 1 → goldMoment ω A k = 0) ∧ A.rank = 2 * t)).card : ℝ) := by sorry

end GoldProxGap
