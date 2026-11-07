-- Prove2me | Theorems.Thm_OWFLocalDesc_lemma_3_1
-- name    : OWFLocalDesc.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:48:11.254945+00:00
-- url     : https://prove2.me/theorems/f68a5dc9-6b90-437c-996f-ddc5f6570829
-- title:
--   Lemma 3.1 (Counting): few label vectors have small quantiles
-- statement:
--   Fix a decoder $U$. For every query clock $t\ge1$, every sample size $m\ge1$, every point vector $x\in(\{0,1\}^n)^m$, every integer $s\ge0$ and every $0<\theta\le1$,
--   $$\Big|\big\{y\in\{0,1\}^m : \mathrm{pSC}^t_\theta(x,y)\le s\big\}\Big|\ \le\ \frac{2^{s+1}}{\theta}.$$
--   Moreover, for every $m\ge1$ and every integer $s\ge0$, at most $2^{s+1}$ certificates $(A,a,\beta)$ for sample size $m$ have charged length at most $s$.
--
--   This is the incompressibility half of the paper: uniformly random labels have large quantiles except with small probability, whatever the decoder does. It holds at every clock and is used in the hardness proof (Theorem 4.5).
--
--   **Formalization Note** The number of certificates is a `Set.encard` in $\mathbb N\cup\{\infty\}$, so the bound also asserts finiteness.
--
--   Differences from the source:
--   - generalization: one efficiently universal Turing machine U, fixed once and for all (§2.1, p.12) → every `Decoder`: any step-indexed machine with the clock, sequential-reading, universality and simulation properties stated in §2.1; reason: §2.1's machine has these properties, so the statement specializes to it
--   - encoding: quantiles in Z≥0 ∪ {∞}; closed intervals of Z ∪ {∞} with ∞ ± d = ∞; ⌈log m⌉ → `pSC` in ℕ∞; the window in `WithTop ℤ` with shifts by `WithTop.map`; `Nat.clog 2 m`; reason: same values and the same order
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Lemma 3.1, p.14

import Mathlib
import Definitions.Def_OWFLocalDesc_pSC
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Lemma 3.1 (Counting).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Lemma 3.1, p.14: "For every query
clock t ≥ 1, every point vector x, every integer s ≥ 0, and every 0 < θ ≤ 1,
|{y : pSC^t_θ(x,y) ≤ s}| ≤ 2^{s+1}/θ. Moreover, for every m ≥ 1 and every integer s ≥ 0, at most
2^{s+1} certificates have charged length at most s."

**Formalization Note.** Both clauses, for every decoder `U` (no universality is used). The second
clause counts triples `(A, a, β)` for fixed `m` with `Set.encard` (in `ℕ∞`, so an infinite set
could not satisfy it). -/
theorem lemma_3_1 (U : Decoder) :
    (∀ (t m n : ℕ), 1 ≤ t → 1 ≤ m → ∀ (x : Fin m → Fin n → Bool) (s : ℕ) (θ : ℝ), 0 < θ → θ ≤ 1 →
      (((Finset.univ.filter fun y : Fin m → Bool => pSC U t θ x y ≤ (s : ℕ∞)).card : ℝ) ≤
        (2 : ℝ) ^ (s + 1) / θ)) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ s : ℕ,
      {c : Certificate m | price c ≤ s}.encard ≤ ((2 ^ (s + 1) : ℕ) : ℕ∞) := by sorry

end OWFLocalDesc
