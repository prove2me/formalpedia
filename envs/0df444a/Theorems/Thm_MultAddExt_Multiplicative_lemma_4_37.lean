-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_lemma_4_37
-- name    : MultAddExt.Multiplicative.lemma_4_37
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:48:57.790628+00:00
-- url     : https://prove2.me/theorems/e53d6e70-2b63-487f-bb80-75cf5cda577b
-- title:
--   Lemma 4.37 — a random line is an averaging sampler: deviation > τ with probability ≤ 1/(4qτ²)
-- statement:
--   Let $\mathbb F_q$ be a finite field with $q$ elements, $d\ge 0$, and $L\leftarrow\mathrm{RandLine}$ the random line $L(t)=u+t(v-u)$ with $u,v$ independent and uniform on $\mathbb F_q^d$. For every $A:\mathbb F_q^d\to[0,1]$ and every $\tau>0$,
--   $$\Pr_{L\leftarrow\mathrm{RandLine}}\Bigl[\Bigl|\mathop{\mathbb E}_{t\leftarrow\mathbb F_q}[A(L(t))]-\mathop{\mathbb E}_{w\leftarrow\mathbb F_q^d}[A(w)]\Bigr|>\tau\Bigr]\le\frac{1}{4q\tau^2}.$$
--
--   It lets the analysis replace averages over $\mathbb F_q^d$ by averages over a random line.
--
--   Differences from the source:
--   - encoding: a (joint) distribution on a finite set → a real mass function p with IsDist p (nonnegative, summing to 1); H∞ = minEntropy (−log₂ of the maximum mass), laws of functions by pushforward; reason: finite distributions are exactly such mass functions; same instances
--   - encoding: L ← RandLine; expectations over t ← F_q and w ← F_q^d → randLineProb over pairs (u, v) uniform on (F^d)²; expectations as averages ∑/q and ∑/q^d; reason: the definition of RandLine (Definition 4.35); same quantities
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 26 (PDF 30), Lemma 4.37

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_FieldCircuits

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Lemma 4.37** (Averaging sampler property of a random line), p. 26. For every
`A : F_q^d → [0, 1]` and `τ > 0`,
`Pr_{L ← RandLine}[ |E_{t ← F_q}[A(L(t))] − E_{w ← F_q^d}[A(w)]| > τ ] ≤ 1/(4qτ²)`. -/
theorem lemma_4_37 {F : Type*} [Fintype F] [Field F] (d : ℕ) (A : (Fin d → F) → ℝ)
    (hA : ∀ w, 0 ≤ A w ∧ A w ≤ 1) (τ : ℝ) (hτ : 0 < τ) :
    randLineProb (fun u v => τ < |(∑ t, A (line u v t)) / (Fintype.card F : ℝ) -
        (∑ w, A w) / (Fintype.card (Fin d → F) : ℝ)|) ≤
      1 / (4 * (Fintype.card F : ℝ) * τ ^ 2) := by sorry

end MultAddExt.Multiplicative
