-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_lemma_5_4
-- name    : NOFSeparation750.CodedGIP.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:43:32.269295+00:00
-- url     : https://prove2.me/theorems/e970cdac-928b-48df-bbf1-8326b0bc335a
-- title:
--   Lemma 5.4 — information-set cylinder transfer
-- statement:
--   Let $k\ge2$, $\ell,r\ge1$, and fix two ordered-basis codes $V,W\le\mathbb F_q^r$. Let $A$ be an accepting cylinder intersection for coded GIP and fix all $k$ large-code words $c^{(i)}\in W$. Write $m=\dim V$, let $\mu$ be uniform on all structured foreheads, and let $\nu$ be uniform on $(\mathbb F_q^{\ell m})^k$. There exist a cylinder intersection $B$ and a field value $\tau$ with
--   $$\nu(B)=\mu(A\mid c^{(1)},\ldots,c^{(k)}),\qquad B\subseteq\{y:\operatorname{GIP}_{q,\ell m}^{k}(y)=\tau\}.$$
--   The fixed-word fiber is nonempty, so the conditional measure is an ordinary positive-denominator cardinality ratio. The source identifies structured foreheads with Boolean strings using bases; both descriptions give the same uniform law. This statement retains exact measure equality and containment in one field-valued fiber.
--
--   Differences from the source:
--   - generalization: the selected compatible codes and Section 3 value of ℓ → arbitrary ordered-basis codes over any finite field and every ℓ≥1; reason: the information-set restriction argument needs only linearity and the whole-vector acceptance identity, so it includes all source instances
--   - encoding: uniform Boolean foreheads identified with codeword tuples → uniform structured foreheads and exact conditional cardinality ratios; reason: the per-forehead basis and binary representation are bijections, preserving cylinders and uniform conditional probabilities
--   - encoding: indices [r] and Boolean values {0,1} → zero-based Fin indices and Bool; reason: order-preserving relabeling changes no inputs, cylinders, or communication costs
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), Lemma 5.4, p.9; §2 information sets, p.6; Definition 3.3, p.7; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Model
import Definitions.Def_NOFSeparation750_CodedGIP_Cylinders

namespace NOFSeparation750.CodedGIP

/-- Lemma 5.4, p.9. Codeword tuples are identified with Boolean foreheads by the
basis bijection of §3. Every fixing of all k large codewords is nonempty. -/
theorem lemma_5_4 (k ℓ r : ℕ) (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (F : Type) [Field F] [Fintype F] (D : CodePair F r)
    (A : Set (Fin k → Forehead D ℓ)) (hA : IsCylinderIntersection A)
    (hAccept : A ⊆ {x | codedGIP D ℓ k x = true})
    (c : Fin k → D.large.code) :
    ∃ B : Set (Fin k → Fin (ℓ * D.small.dimension) → F), ∃ τ : F,
      IsCylinderIntersection B ∧
      uniformMass B = conditionalMass A {x | ∀ i, (x i).2 = c i} ∧
      B ⊆ {y | gip y = τ} := by sorry

end NOFSeparation750.CodedGIP
