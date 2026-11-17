-- Prove2me | Theorems.Thm_LinSSWorst_Supplement_theorem_6_2
-- name    : LinSSWorst.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:49:38.226184+00:00
-- url     : https://prove2.me/theorems/e8d5e8ae-e983-48d9-8fff-79e497e70652
-- title:
--   Theorem 6.2 (Quadratic midslice schemes) — every $\delta$-midslice has a quadratic scheme with total share size $2^{Q(\delta)n+o(n)}$
-- statement:
--   For every constant $\delta\in(0,1/2)$ there is a function $g(n)=o(n)$ such that every $\delta$-midslice function over $n$ parties can be realized by a secret-sharing scheme for one-bit secrets with quadratic sharing and reconstruction and total share size at most
--   $$2^{Q(\delta)\,n+g(n)},\qquad Q(\delta)=\begin{cases}\frac13+\frac{1+2\delta}{3}H_2\!\left(\frac{1-2\delta}{1+2\delta}\right),&0<\delta\le\frac16,\\ \frac23+\frac{2\delta}3,&\frac16\le\delta<\frac12.\end{cases}$$
--
--   This replaces the non-linear midslice scheme of [ABNP20] in the proof of Theorem 1.6.
--
--   **Formalization Note** Quadratic schemes are over $\mathbb F_2$; total share size is $\sum_i\ell_i$ bits; $H_2$ is the base-two binary entropy.
--
--   Differences from the source:
--   - reading: total share size 2^{Q(δ)n+o(n)} → ∃ g =o[atTop] n (depending on δ only) with Σ ℓ_i ≤ 2^{Q(δ)n + g(n)}; reason: a realization bound is an upper bound; g is uniform over n and the midslice
--   - reading: quadratic sharing and reconstruction, field unspecified → over F₂ with one-bit secrets; reason: one-bit secrets and [BOP21] schemes compute over the field of the secret
--   - encoding: Q(δ) with overlapping branches at δ = 1/6 → first branch for δ ≤ 1/6, second for δ > 1/6; reason: both equal 7/9 at δ = 1/6
--   - generalization: δ-midslice defined only when a = ⌈(1/2 − δ)n⌉ ≤ b = ⌊(1/2 + δ)n⌋ (Definition A.7 takes a ≤ b ∈ [n]) → the case formula also for the finitely many small n with a > b (then F(x) = 1 iff wt(x) ≥ a, an access structure); reason: a > b forces n < 1/(2δ), so only finitely many n gain instances, each has some quadratic scheme, and g absorbs them; on every n the source covers the two statements coincide
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 6.2, p.19; proof App. B.2, pp.33–34; Definition A.7, pp.30–31

import Mathlib
import Definitions.Def_LinSSWorst_Supplement_RealizesQuad
import Definitions.Def_LinSSWorst_Supplement_IsMidslice
import Definitions.Def_LinSSWorst_Supplement_Qexp

open Asymptotics

namespace LinSSWorst.Supplement

/-- **Theorem 6.2 (Quadratic midslice schemes)**, p.19 (proved in App. B.2, pp.33–34), from O. Nir,
*Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission, version of
2026-11-02, sha256 5521cfdb…). For every constant `δ ∈ (0, 1/2)` there is a function `g(n) = o(n)` such that
every `δ`-midslice function over `n` parties can be realized by a secret-sharing scheme for one-bit secrets
with quadratic sharing and reconstruction and total share size at most `2^{Q(δ) n + g(n)}`, where
`Q(δ) = 1/3 + ((1 + 2δ)/3) H₂((1 − 2δ)/(1 + 2δ))` for `0 < δ ≤ 1/6` and `Q(δ) = 2/3 + 2δ/3` for
`1/6 ≤ δ < 1/2`.

**Formalization Note.** "Total share size `2^{Q(δ)n+o(n)}`" is read as an upper bound, with one function
`g =o[atTop] n` that may depend on `δ` but not on `n` or the midslice. Quadratic schemes are over `F₂` with
one-bit secrets (`RealizesQuad`), total share size `Σ_i ℓ_i` bits. `δ`-midslices are Definition A.7 with
`a = ⌈(1/2 − δ) n⌉`, `b = ⌊(1/2 + δ) n⌋`; `H₂` is the base-two binary entropy. -/
theorem theorem_6_2 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ g : ℕ → ℝ, g =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) ∧
      ∀ (n : ℕ) (F : (Fin n → Bool) → Bool), IsMidslice δ F →
        ∃ (ℓr : ℕ) (ℓ : Fin n → ℕ)
          (sh : (i : Fin n) → Fin (ℓ i) → MvPolynomial (Option (Fin ℓr)) (ZMod 2)),
          RealizesQuad F sh ∧
            ((∑ i, ℓ i : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Qexp δ * n + g n) := by sorry

end LinSSWorst.Supplement
