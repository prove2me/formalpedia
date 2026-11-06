-- Prove2me | Theorems.Thm_OrderedExperts_lemma_3
-- name    : OrderedExperts.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:34:24.390216+00:00
-- url     : https://prove2.me/theorems/01ee06d6-9434-40dc-a91c-5ba551c4f4d1
-- title:
--   Lemma 3 — second moment of the flow estimator
-- statement:
--   Under the assumptions of Lemma 1 (a probability law $P$ of the queried pair on $\{1,\dots,m\}^2$, nonnegative flows $\varphi_j$, and for every target $j$ the support condition and the flow identity), let $\pi$ be nonnegative weights on the active ranks. Then
--   $$
--   \mathbb E\,\langle \pi,\hat g^2\rangle\le 2\sum_{e:\,q(e)>0}\frac{H(e)^2}{q(e)}\sum_{j}\pi(j)\varphi_j(e)^2,
--   $$
--   where $\langle\pi,\hat g^2\rangle=\sum_{j=1}^m\pi(j)\hat g(j)^2$, $H(0,a)=g(x_a)$, $H(a,b)=g(x_b)-g(x_a)$, and the outer sum runs over anchor edges $(0,a)$ and interval edges $(a,b)$, $1\le a<b\le m$, with positive revelation probability.
--
--   Each edge contributes its squared increment times its load relative to its revelation probability; Lemmas 4 and 5 bound these two factors.
--
--   Differences from the source:
--   - generalization: $\pi$ the intended distribution on the ranks → any nonnegative weights on the active ranks; reason: the bound is linear in $\pi$ and holds for each nonnegative weight; a distribution is a special case
--   - encoding: expectation over a random pair → the finite sum $\sum_{A,B}P(A,B)\,\cdot$; reason: finite probability space; same instances
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Lemma 3, p.9; Appendix A.1, p.17

import Definitions.Def_OrderedExperts_genEst
open Finset

namespace OrderedExperts

/-- **Lemma 3 (Second moment).** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Lemma 3, p.9: "Under the assumptions of
Lemma 1, `E⟨π, ĝ²⟩ ≤ 2 Σ_e H(e)²/q(e) Σ_j π(j)φj(e)²`, where the outer sum runs over edges with
`q(e) > 0`."

Under the assumptions of Lemma 1 (for every target `j`), and for nonnegative weights `π` on the active
ranks, the `P`-expectation of `Σ_j π(j) ĝ(j)²` is at most twice the sum, over anchor edges `(0, a)` and
interval edges `(a, b)` with positive revelation probability, of `H(e)²/q(e) · Σ_j π(j)φj(e)²`.

**Formalization Note.** `H(0, a) = g a` (`g(x0) = 0`), `H(a, b) = g b − g a`; the targets and edges
range over the active ranks `1, …, m`. -/
theorem lemma_3 (m : ℕ) (P : ℕ → ℕ → ℝ) (hP : ∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m, 0 ≤ P a b)
    (hP1 : ∑ a ∈ Icc 1 m, ∑ b ∈ Icc 1 m, P a b = 1)
    (φ : ℕ → ℕ → ℕ → ℝ) (hφ : ∀ j a b, 0 ≤ φ j a b) (g : ℕ → ℝ)
    (hsupp0 : ∀ j ∈ Icc 1 m, ∀ a ∈ Icc 1 m, 0 < φ j 0 a → 0 < revAnchor m P a)
    (hsuppI : ∀ j ∈ Icc 1 m, ∀ a ∈ Icc 1 m, ∀ b ∈ Ioc a m, 0 < φ j a b → 0 < revInterval P a b)
    (hflow : ∀ j ∈ Icc 1 m, g j = ∑ a ∈ Icc 1 m, φ j 0 a * g a +
      ∑ a ∈ Icc 1 m, ∑ b ∈ Ioc a m, φ j a b * (g b - g a))
    (π : ℕ → ℝ) (hπ : ∀ j ∈ Icc 1 m, 0 ≤ π j) :
    ∑ A ∈ Icc 1 m, ∑ B ∈ Icc 1 m, P A B * ∑ j ∈ Icc 1 m, π j * genEst m P φ g A B j ^ 2 ≤
      2 * (∑ a ∈ (Icc 1 m).filter (fun a => 0 < revAnchor m P a),
            g a ^ 2 / revAnchor m P a * ∑ j ∈ Icc 1 m, π j * φ j 0 a ^ 2 +
          ∑ a ∈ Icc 1 m, ∑ b ∈ (Ioc a m).filter (fun b => 0 < revInterval P a b),
            (g b - g a) ^ 2 / revInterval P a b * ∑ j ∈ Icc 1 m, π j * φ j a b ^ 2) := by sorry

end OrderedExperts
