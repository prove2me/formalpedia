-- Prove2me | Theorems.Thm_FuchsThesis_HonestExpert_eq_2_66
-- name    : FuchsThesis.HonestExpert.eq_2_66
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:27.963995+00:00
-- url     : https://prove2.me/theorems/65fc2ac5-a099-426b-a16f-573ef8dd29b0
-- title:
--   (2.66) — differentiability of $F_2$ at $r-p$ gives $pF_1'(p)=(r-p)F_2'(r-p)$
-- statement:
--   Let $n \ge 3$, let $F_1, \dots, F_n$ keep the expert honest, let $i \ne j$ be two outcomes and let $0 < p < r < 1$. If $F_j$ is differentiable at $r - p$, then $F_i$ is differentiable at $p$ and
--
--   $$p\,F_i'(p) \;=\; (r - p)\,F_j'(r - p) .$$
--
--   Since $r$ can be any number in $(p, 1)$, the contrapositive says: if $F_i$ fails to be differentiable at a single point $p$, then $F_j$ fails to be differentiable at every point of $(0, 1 - p)$. Combined with Lebesgue's theorem (Lemma 2.1) this forces all honest payoffs to be differentiable on $(0,1)$, and the identity (2.66), with $p$ and $s = r - p$ independent, forces $pF_i'(p)$ to be a constant.
--
--   Differences from the source:
--   - generalization: F₁ at p and F₂ at r − p → F_i at p and F_j at r − p for any two distinct outcomes; reason: p.24 runs the same argument for the pair (1, k); i = 1, j = 2 gives the page's case
--   - reading: (2.45) for all n-point distributions → (2.45) for all strictly positive n-point distributions; reason: the positivity reading of Theorem 2.3; the hypothesis is weaker
--   - encoding: outcomes 1, …, n → Fin n; F′ → the two-sided derivative of F_k : ℝ → ℝ at an interior point of (0, 1); reason: Lean conventions; at interior points the derivative depends only on F_k on (0, 1)
--   - encoding: real payoffs F_k defined on [0, 1] → real functions F_k defined on all of ℝ; reason: only values on (0, 1) enter (the coordinates of strictly positive distributions for n ≥ 3); any F_k on [0, 1] extends to ℝ and the extension changes no clause
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3.1, eqs. (2.63)–(2.66), p.23 (PDF p.32)

import Mathlib
import Definitions.Def_FuchsThesis_HonestExpert_KeepsHonest

namespace FuchsThesis.HonestExpert

/-- **(2.66): differentiability transfers from `F₂` at `r − p` to `F₁` at `p`.**
Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1,
§2.3.1, eqs. (2.63)–(2.66), p.23 (PDF p.32): "In other words, if F₂ is differentiable at (r − p),
then F₁ is differentiable at p and p F₁′(p) = (r − p) F₂′(r − p)."

For `n ≥ 3`, payoffs `F` keeping the expert honest, outcomes `i ≠ j` (the page's `1, 2`) and reals
`0 < p < r < 1`: if `F_j` is differentiable at `r − p`, then `F_i` is differentiable at `p` and
`p F_i′(p) = (r − p) F_j′(r − p)`.

**Formalization Note.** `DifferentiableAt` and `deriv` are the ordinary two-sided derivative of
`F_k : ℝ → ℝ`; since `p` and `r − p` lie in the open interval `(0, 1)`, they depend only on the
values of `F_k` on `(0, 1)`. -/
theorem eq_2_66 {n : ℕ} (hn : 3 ≤ n) {F : Fin n → ℝ → ℝ} (hF : KeepsHonest F)
    {i j : Fin n} (hij : i ≠ j) {p r : ℝ} (hp : 0 < p) (hpr : p < r) (hr : r < 1)
    (hd : DifferentiableAt ℝ (F j) (r - p)) :
    DifferentiableAt ℝ (F i) p ∧ p * deriv (F i) p = (r - p) * deriv (F j) (r - p) := by sorry

end FuchsThesis.HonestExpert
